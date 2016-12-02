/*
 * Author: Markus Kusano
 *
 * Interprocedural context-insensitive program dependence graph
 *
 * Outputs all the control and data dependency, and alias information to a
 * datalog file.
 *
 * Output is in SMT-Lib2 format with support for rules and queries, see:
 * http://rise4fun.com/Z3/tutorialcontent/fixedpoints
 *
 * Note: This pass requires the PostDominatorTree pass to be run
 */

#include "llvm/Pass.h"
//#include "llvm/IR/Instruction.h"
//#include "llvm/IR/Module.h"
//#include "llvm/IR/Instructions.h"
//#include "llvm/Support/raw_ostream.h"
//#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Analysis/PostDominators.h"

#include "../ContextInsenAA/FactVisitor.h"
#include "ControlDependence.h"

#include "../utils/utils.h"
#define MK_DEBUG
#include "../utils/mk_debug.h"

#include <string>

using namespace llvm;

struct ContextInsenPDG : ModulePass {
  static char ID;
  ValToStrDB IDMap;

  ContextInsenPDG() : ModulePass(ID) { }

  void addSpec(raw_fd_ostream &f) {
    // TODO: need to figure out the specification to use
    DEBUG_MSG("[WARNING] addSpec(): unimplemented\n");
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    // For control dependence analysis
    AU.addRequired<PostDominatorTree>();
    AU.setPreservesAll();
  }

  // Given the passed name of a function, return the name of its return
  // instruction. This allows for other functions to setup alias links to the
  // return value
  std::string getFuncReturnName(StringRef funcName) {
    assert(funcName.size() 
        && "Size zero function name passed to getFuncReturnName");
    std::string ret = funcName;
    return ret + "_RETURN";
  }

  // The passed string should be string IDs from a ValToStrDB. These will be
  // converted to integer IDs (bitvectors)
  std::string createCDep(std::string to, std::string from) {
    assert(to.size() && "emtpy to string");
    assert(from.size() && "emtpy from string");

    // Convert to integer Ids
    to = Utils::to_const_bitvec(IDMap.saveAndGetIntID(to));
    from = Utils::to_const_bitvec(IDMap.saveAndGetIntID(from));

    return "(rule (control-dep " + to + ' ' + from + "))";
  }

  // Create a control dependence from-->to in the passed ostream. 
  std::string createCDep(Value *to, Value *from) {
    DEBUG_MSG("createCDep():\n");
    DEBUG_MSG("\tto: " << *to << ' ' << to << '\n' 
          << "\tfrom: " << *from << '\n');

    assert(to && "NULL passed");
    assert(from && "NULL passed");

    // Get the string Ids
    std::string toStrId = IDMap.saveAndGetID(to);
    std::string fromStrId = IDMap.saveAndGetID(from);

    DEBUG_MSG("\ttoStrID: " << toStrId << '\n'
        << "\tfromStrID: " << fromStrId << '\n');


    return createCDep(toStrId, fromStrId);

    //(*out) << "(rule (control-dep " << toStrId << ' ' << fromStrId << "))\n";
  }

  // Remove one star from the value being dereferenced (from) and create an
  // assignment from-->to.
  //
  // Control dependencies will be created to the derefenced values from the
  // passed instruction
  std::string createStore(Value *to, Value *from, Instruction *i) {
    assert(to && "NULL passed");
    assert(from && "NULL passed");

    assert(to->getType() && "to value with NULL type");
    assert(to->getType()->isPointerTy() && "to value that is not a pointer");
    assert(from->getType()->isPointerTy() && "to value that is not a pointer");

    // Currently only support storing to some types:
    // Storing an {instruction, function argument, global variable} in a
    // {global, instruction}
    DEBUG_MSG("createStore():\n\tto: "<< *to << "\n\tfrom" << *from << '\n');
    std::string toStr = IDMap.saveAndGetID(to);
    DEBUG_MSG("\ttoStr: " << toStr << '\n');
    // Get the ID of the dereferenced form of the from pointer
    std::string fromStr = IDMap.saveAndGetID(from);
    DEBUG_MSG("\tfromStr: " << fromStr << '\n');

    // Remove one star from the value being stored(i.e., the pointer operand).
    // This represents it being dereferenced once.
    //
    // The dereferenced string is not actually a value in the program. It is
    // simply a temporary node in the graph which is used to hook up with
    // subsequent loads. It is not stored in the ValToStrDB and thus will not be
    // found in the module's metadata. After the analysis is done, it can be
    // discarded.
    std::string derefTo = ValToStrDB::rmStar(toStr);

    // When we dereference a pointer we create a new (and unique) node in the
    // program dependence graph. We need to connect it with its parent (e.g.,
    // the store, which is a dereferenced pointer assignment, should have the
    // same control dependencies as its parent). 
    //std::string ret = createAssign(derefTo, toStr);
    
    // The instruction performing the store is data dependent on the pointer
    // being stored into
    std::string ret = createAssign(IDMap.saveAndGetID(i), toStr);

    // The instruction performing the store is data dependent on the value
    // being stored
    ret += "\n";
    ret += createAssign(IDMap.saveAndGetID(i), fromStr);

    // The dereferenced pointer is data dependent on the store instruction.
    // This a forward slice on the store will touch everything which touched
    // the pointer moditified by the store
    ret += "\n";
    ret += createAssign(derefTo, IDMap.saveAndGetID(i));
    

    // Assigning to the derefenced pointer the value operand
    // Since the store instruction is already data dependent on fromStr the
    // dereferenced pointer does not need to be.
    //ret += "\n";
    //ret += createAssign(derefTo, fromStr);

    return ret;
  }

  // Create a memcpy from-->to. This will dereference both of the passed values
  std::string createMemCpy(Value *to, Value *from) {
    assert(to && "NULL Passed");
    assert(from && "NULL Passed");

    assert(from->getType() && "from value with NULL type");
    assert(from->getType()->isPointerTy() 
        && "from value that is not a pointer");
    assert(to->getType()->isPointerTy() 
        && "to value that is not a pointer");

    std::string toStr = IDMap.saveAndGetID(to);
    // Get the ID of the dereferenced form of the from pointer
    std::string fromStr = IDMap.saveAndGetID(from);

    std::string derefFrom = ValToStrDB::rmStar(fromStr);
    std::string derefTo = ValToStrDB::rmStar(toStr);

    // When we dereference a pointer we create a new (and unique) node in the
    // program dependence graph. We need to connect it with its parent (e.g.,
    // the store, which is a dereferenced pointer assignment, should have the
    // same control dependencies as its parent). 
    std::string ret = createAssign(derefTo, toStr);
    ret += "\n";
    ret += createAssign(derefFrom, fromStr);
    ret += "\n";
    ret += createAssign(derefTo, derefFrom);
    return ret;
  }

  // Create a data dependence from-->to assuming that the values come from a
  // load. This will dereference the from value.
  //
  // The passed instruction is the instruction actually performing the load.
  // The dereferenced values will be come control dependent on the passed
  // instruction. This ensures that the dereferenced values keep their parents
  // control dependencies
  std::string createLoad(Value *to, Value *from, Instruction *i) {
    assert(to && "NULL Passed");
    assert(from && "NULL Passed");

    assert(from->getType() && "from value with NULL type");
    assert(from->getType()->isPointerTy() 
        && "from value that is not a pointer");
    assert(to->getType()->isPointerTy() 
        && "from value that is not a pointer");

    if (!(isa<Instruction>(from)
        || isa<Argument>(from)
        || isa<GlobalVariable>(from))) {
      DEBUG_MSG("[ERROR] Unhandled load pointer operand type: " 
          << *from << '\n');
      llvm_unreachable("unhandled load type (see above)");
    }

    std::string toStr = IDMap.saveAndGetID(to);
    // Get the ID of the dereferenced form of the from pointer
    std::string fromStr = IDMap.saveAndGetID(from);

    // Remove one star from the to. This represents it being dereferenced
    // once. That is, in a store instruction, the pointer operand is dereferenced
    // and then assigned.
    //
    // The dereferenced string is not actually a value in the program. It is
    // simply a temporary node in the graph which is used to hook up with
    // subsequent loads. It is not stored in the ValToStrDB and thus will not be
    // found in the module's metadata. After the analysis is done, it can be
    // discarded.
    std::string derefFrom = ValToStrDB::rmStar(fromStr);


    // When we dereference a pointer we create a new (and unique) node in the
    // program dependence graph. We need to connect it with its parent (e.g.,
    // the store, which is a dereferenced pointer assignment, should have the
    // same control dependencies as its parent). 
    //std::string ret = createAssign(derefFrom, fromStr);

    // The instruction performing the load is data dependent on the pointer
    // being loaded
    std::string ret = createAssign(IDMap.saveAndGetID(i), fromStr);

    // create a oontrol dependency to the dereferenced value from the
    // instruction
    // Markus: This control dependency is not necessary. The load is simply a
    // flow of data not control
    //ret += "\n";
    //ret += createCDep(derefFrom, IDMap.saveAndGetID(i));
    ret += "\n";
    ret += createAssign(toStr, derefFrom);
    return ret;
  }

  std::string createAssign(std::string to, std::string from) {
      std::string ret;
    DEBUG_MSG("createAssign():\n");
    // Convert the string keys to integers
    DEBUG_MSG("\tpreConvert from: " << from << '\n');
    to = Utils::to_const_bitvec(IDMap.saveAndGetIntID(to));
    from = Utils::to_const_bitvec(IDMap.saveAndGetIntID(from));
    //DEBUG_MSG("\tfromID: " << IDMap.saveAndGetIntID(from) << '\n');
    //DEBUG_MSG("\ttoStr: " << to << "\n\tfromStr" << from << '\n');

    ret = "(rule (assign " + to + ' ' + from + "))";

    assert(ret.size());
    return ret;
  }

  std::string createAssign(Value *to, Value *from) {
    assert(to != NULL && "NULL Passed");
    assert(from != NULL && "NULL Passed");
    // Attempt to convert to and from to values which are handled

    std::string toStr = IDMap.saveAndGetID(to);
    std::string fromStr = IDMap.saveAndGetID(from);

    return createAssign(toStr, fromStr);
  }

  std::string visitAllocaInst(AllocaInst *I) {
    assert(I->getType() && "Alloca with NULL type");
    assert(I->getType()->isPointerTy() && "pointer type");

    static int counter = 0;
    // Create the stack object
    std::string stackStr = "stack_" + std::to_string(counter);
    counter += 1;

    // Create an assignment to the return of the alloca (the instruction) from a
    // the stack object
    std::string fact = createAssign(IDMap.saveAndGetID(I), stackStr);
    return fact;
  }

  std::string visitAtomicCmpXchg(AtomicCmpXchgInst *i) {
    std::string ret;
    // An atomic compare exchange is basically a conditional store
    Value *ptr = i->getPointerOperand();
    Value *cmp = i->getCompareOperand();
    Value *newVal = i->getNewValOperand();
    assert(ptr && "cmpxchg with NULL pointer");
    assert(cmp && "cmpxchg with NULL compare");
    assert(newVal && "cmpxchg with NULL new value");

    // First, create a store to the pointer from the new value
    ret = createStore(ptr, newVal, i);

    // create store dereferences the pointer operand and makes the dereferenced
    // value dependent on the new value.
    // The compare operand is essentially another data (or maybe more like a
    // control) dependency on the dereferenced pointer operand: depending on
    // its value the dereferenced pointer is either modified or not. As a
    // result, it can be handled in the same way as a store
    ret += '\n';
    ret += createStore(ptr, cmp, i);

    // cmpxchg also returns the original value. This is essentially a load from
    // the dereferenced pointer to the return of the instruction
    ret += '\n';
    ret += createLoad(i, ptr, i);
    assert(ret.size() && "ret not set");
    return ret;
  }

  std::string visitGetElementPtrInst(GetElementPtrInst *i) {
    // TODO: Currentlly no interpretation of getelementptr is done. Atleast
    // three improvements could be made:
    //
    // 1. Consider calls with the same base pointer but different offsets to be
    // different values
    // 2. Consider calls with different type offsets to be different values
    // 3. Further follow nested offsets
    assert(i && "NULL passed");
    Value *ptr = i->getPointerOperand();
    assert(ptr && "getelementptr with NULL pointer");
    return createAssign(i, ptr);
  }

  std::string visitAtomicRMWInst(AtomicRMWInst *i) {
    assert(i && "NULL passed");
    Value *val = i->getValOperand();
    Value *ptr = i->getPointerOperand();

    std::string ret = "";

    // First, an atomicRMW is a store to the pointer value
    ret += createStore(ptr, val, i);

    // Next, an atomicRMW loads the value from the address to the return
    ret += "\n";
    ret += createLoad(i, ptr, i);
    return ret;
  }

  std::string visitStoreInst(StoreInst *i) {
    Value *val = i->getValueOperand();
    Value *ptr = i->getPointerOperand();
    std::string ret;
    ret = createStore(ptr, val, i);
    assert(ret.size() && "ret not set");
    return ret;
  }

  std::string visitLoadInst(LoadInst *i) {
    std::string ret;
    Value *ptr = i->getPointerOperand();
    ret = createLoad(i, ptr, i);
    assert(ret.size() && "ret not set");
    return ret;
  }

  std::string visitReturnInst(ReturnInst *i) {
    DEBUG_MSG("Visiting RetInst: " << *i << '\n');
    Value *retVal = i->getReturnValue();
    if (retVal == NULL) {
      llvm_unreachable("visiting return inst without a return");
    }

    // Get the name of the function containing the return inst. Each function
    // has a special return value name which aliases to all the return points
    // of the function
    StringRef funcName = i->getParent()->getParent()->getName();
    assert(funcName.size() && "Returning from function with no name");
    DEBUG_MSG("\tFunction Name: " << funcName << '\n');
    // Identifier for function return
    std::string funcRetName = getFuncReturnName(funcName);

    // First create a data dependency from the value being returned to the
    // return instruction
    std::string ret = "";
    ret += createAssign(i, retVal);

    // Next, link the return instruction to the return node for the function:
    // this connects all the return nodes of a function together. When visiting
    // a call instruction, the return of the call will be linked to this
    // "global" function return node.
    ret += "\n";
    ret += createAssign(funcRetName, IDMap.saveAndGetID(i));
  

    // Handle the different types of possible pointers returned.
#if 0
    if (Instruction *retValInst = dyn_cast<Instruction>(retVal)) {


      // Create an assignment from the value being returned (retValInst) to the
      // global return of the function. This allows for other functions to
      // connect witth the return value.
      //
      // Note: this approximates all return instructions of a function to alias
      // together
      ret += createAssign(funcRetName, IDMap.saveAndGetID(retValInst));
    }
    else if (ConstantPointerNull *cn = dyn_cast<ConstantPointerNull>(retVal)) {
      std::string constID = ValToStrDB::Constants::getStr(cn);
      // The function return is assigned the constant ID
      ret += createAssign(funcRetName, constID);
    }
    else {
      // TODO: Probably need to handle other types
      DEBUG_MSG("[ERROR] Non instruction return: " << *retVal << '\n');
      llvm_unreachable("Non instruction return value (see above)");
    }
#endif

    assert(ret.size() && "ret not set");
    return ret;
  }

  std::string handleCallSite(CallSite I) {
    std::string ret;
    DEBUG_MSG("Visiting CallSite: " << *(I.getInstruction()) << "\n");
    DEBUG_MSG("\tType? " << *(I.getType()) << '\n');

    Function *callee = I.getCalledFunction();
    assert(callee != NULL && "Calling indirect function");

    StringRef funcName = callee->getName();
    assert(funcName.size() && "Calling function without name");

    // Get the ID of the callsite instruction
    Instruction *cs = I.getInstruction();

    // Create an alias link from the return instruction to the return of the
    // function
    // Each function has a node for its return value (see visitReturnInst())
    std::string funcRetName = getFuncReturnName(funcName);
    // Create an assignment to the CallSite (the return) to the return of the
    // function.
    ret = createAssign(IDMap.saveAndGetID(cs), funcRetName);

    DEBUG_MSG("\tHandling callsite arguments\n");

    for (auto i = callee->arg_begin(), e = callee->arg_end(); i != e; ++i) {
      Argument &a = *i;

      // Get an ID to the operand used in the caller
      Value *callerOp = I.getArgument(a.getArgNo());
      assert(callerOp && "argument not found on caller");

      // Link the function argument to the callsite argument
      DEBUG_MSG("\tLinking function arg to callsite arg\n");
      //std::string fact = createAssign(&a, fromOp);
      std::string fact = createAssign(&a, callerOp);
      //writeFact(I.getInstruction(), fact);
      ret += "\n";
      ret += fact;
    }
    DEBUG_MSG("Finished callsite\n");
    assert(ret.size() && "ret not set");
    return ret;
  }

  virtual bool runOnModule(Module &M) {
    DEBUG_MSG_RED("Starting context insensitive PDG pass\n");

    // Use the name of the module as the filename
    std::string modName = M.getModuleIdentifier();
    assert(modName.size() && "Module ID has size zero");
    std::string path;
    path = modName + ".smt2";
    assert(path.size() && "empty output file path");


    // Attempt to open a stream to the passed path, crash on failure.
    std::string ec;
    // Open file in text mode
    raw_fd_ostream *outFile = new raw_fd_ostream(path.c_str(), ec
        , sys::fs::OpenFlags::F_Text);
    if (!ec.empty()) {
      errs() << "[ERROR] Unable to open file " << path << ": " << ec 
             << '\n';
      exit(EXIT_FAILURE);
    }

    // Prepend the specification to the file
    addSpec(*outFile);

    (*outFile) << "\n; Begin Facts\n\n";

    // Calculate the control and data dependencies:
    //
    // First: Find the control dependencies of every basic block. Every
    // instruction inside a BasicBlock is control dependent on the dependencies
    // of the BasicBlock
    //
    // Second: find the immediate data dependency of each instruction. Since we
    // are visiting each instruction, we only need to do one-hop on the use-def
    // chain: after visiting every instructions we will have dumped the entire
    // use-def chain.
    ControlDependence cdep;

    // don't visit the same instruction twice
    std::set<Instruction *> visited;
    for (auto mi = M.begin(), me = M.end(); mi != me; ++mi) {
      Function &f = *mi;
      // Calculate the post-dominator tree of the function. This is required
      // for the control dependency analysis
      PostDominatorTree &PDT = getAnalysis<PostDominatorTree>(f);
      // Calculate the control dependencies of all the basic blocks in the
      // function
      cdep.getControlDependencies(f, PDT);

      for (auto fi = f.begin(), fe = f.end(); fi != fe; ++fi) {
        BasicBlock &bb = *fi;
        // Get all the basic blocks whic the current basic block is control
        // dependent on
        auto cds = cdep.reverseControlDeps_.find(&bb);
        // Gather all the terminator instructions: all the nodes in the PDG are
        // instructions, not basic blocks
        std::set<TerminatorInst *> ts;
        if (cds != cdep.reverseControlDeps_.end()) {
          std::set<BasicBlock *> bbs = cds->second;
          for (auto si = bbs.begin(), se = bbs.end(); si != se; ++ si) {
            TerminatorInst *ti = (*si)->getTerminator();
            assert(ti && "malformed basic block");
            ts.insert(ti);
          }
        }

        for (auto bi = bb.begin(), be = bb.end(); bi != be; ++bi) {
          Instruction &I = *bi;
          if (visited.find(&I) != visited.end()) {
            continue;
          }
          visited.insert(&I);
          // Mark this instruction as control dependent on all the terminator
          // instructions controlling its basic block
          for (auto ti = ts.begin(), te = ts.end(); ti != te; ++ti) {
            // Create a control dependence edge to the instruction from the
            // terminator
            (*outFile) << createCDep(&I, *ti) << "\n";
          }
          DEBUG_MSG("Iterating over use-def of: " << I << '\n');

          // Generate a fact based on the instruction type
          std::string fact;

          // Different instruction types have different data dependencies
          // depending on the semantics of the instruction
          if (ReturnInst *i = dyn_cast<ReturnInst>(&I)) {
            if (!i->getReturnValue()) {
              continue;
            }
            fact = visitReturnInst(i);
          }
          else if (StoreInst *i = dyn_cast<StoreInst>(&I)) {
            fact = visitStoreInst(i);
          }
          else if (LoadInst *i = dyn_cast<LoadInst>(&I)) {
            fact = visitLoadInst(i);
          }
          else if (CallInst *i = dyn_cast<CallInst>(&I)) {
            CallSite cs = CallSite(i);
            fact = handleCallSite(cs);
          }
          else if (InvokeInst *i = dyn_cast<InvokeInst>(&I)) {
            CallSite cs = CallSite(i);
            fact = handleCallSite(cs);
          }
          else if (AllocaInst *i = dyn_cast<AllocaInst>(&I)) {
            fact = visitAllocaInst(i);
          }
          else if (BranchInst *i = dyn_cast<BranchInst>(&I)) {
            // unconditional branches have no data dependencies
            if (i->isUnconditional()) {
              continue;
            }
            Value *cond = i->getCondition();
            assert(cond && "branch with NULL condition");
            fact = createAssign(i, cond);
          }

          else if (SwitchInst *i = dyn_cast<SwitchInst>(&I)) {
            Value *cond = i->getCondition();
            assert(cond && "switch with NULL condition");
            fact = createAssign(i, cond);
          }
          else if (IndirectBrInst *i = dyn_cast<IndirectBrInst>(&I)) {
            Value *addr = i->getAddress();
            fact = createAssign(i, addr);
          }
          else if (ResumeInst *i = dyn_cast<ResumeInst>(&I)) {
            Value *v = i->getValue();
            fact = createAssign(i, v);
          }
          else if (CmpInst *i = dyn_cast<CmpInst>(&I)) {
            assert(i->getNumOperands() == 2 
                && "CmpInst w/o two operands");
            Value *op0 = i->getOperand(0);
            Value *op1 = i->getOperand(1);
            fact = createAssign(i, op0);
            fact += "\n";
            fact += createAssign(i, op1);
          }
          else if (isa<ICmpInst>(&I)) {
            // TODO: I believe this is handled by CmpInst 
            llvm_unreachable("unimplemented");
          }
          else if (AtomicCmpXchgInst *i = dyn_cast<AtomicCmpXchgInst>(&I)) {
            fact = visitAtomicCmpXchg(i);
          }
          else if (AtomicRMWInst *i = dyn_cast<AtomicRMWInst>(&I)) {
            fact = visitAtomicRMWInst(i);
          }
          else if (isa<FenceInst>(&I)) {
            // TODO: What should a fence instruction be dependent on?
            // Technically it affects all the prior memory modifications
            DEBUG_MSG("Unhandled: fenceInst" << *i << '\n');
            llvm_unreachable("unimplemented");
          }
          else if (GetElementPtrInst *i = dyn_cast<GetElementPtrInst>(&I)) {
            fact = visitGetElementPtrInst(i);
          }
          else if (isa<PHINode>(&I)) {
            llvm_unreachable("PHI inst unimplemented");
          }
          else if (CastInst *i = dyn_cast<CastInst>(&I)) {
            assert(i->getNumOperands() == 1 && "CastInst w/o 1 operand");
            Value *op = i->getOperand(0); 
            fact = createAssign(i, op);
          }
          // The previous CastInst check should handle all of the following
          // cast child classes
          else if (isa<TruncInst>(&I)) {
            llvm_unreachable("should be handled by CastInst");
          }
          else if (isa<ZExtInst>(&I)) {
            llvm_unreachable("should be handled by CastInst");
          }
          else if (isa<SExtInst>(&I)) {
            llvm_unreachable("should be handled by CastInst");
          }
          else if (isa<FPTruncInst>(&I)) {
            llvm_unreachable("should be handled by CastInst");
          }
          else if (isa<FPExtInst>(&I)) {
            llvm_unreachable("should be handled by CastInst");
          }
          else if (isa<FPToUIInst>(&I)) {
            llvm_unreachable("should be handled by CastInst");
          }
          else if (isa<FPToSIInst>(&I)) {
            llvm_unreachable("should be handled by CastInst");
          }
          else if (isa<UIToFPInst>(&I)) {
            llvm_unreachable("should be handled by CastInst");
          }
          else if (isa<SIToFPInst>(&I)) {
            llvm_unreachable("should be handled by CastInst");
          }
          else if (isa<PtrToIntInst>(&I)) {
            llvm_unreachable("should be handled by CastInst");
          }
          else if (isa<IntToPtrInst>(&I)) {
            llvm_unreachable("should be handled by CastInst");
          }
          else if (isa<BitCastInst>(&I)) {
            llvm_unreachable("should be handled by CastInst");
          }
          else if (isa<AddrSpaceCastInst>(&I)) {
            llvm_unreachable("should be handled by CastInst");
          }
          else if (SelectInst *i = dyn_cast<SelectInst>(&I)) {
            Value *cond = i->getCondition();
            Value *trueVal = i->getTrueValue();
            Value *falseVal = i->getFalseValue();
            // The instruction depends on all three values. It is sort of a
            // data dependency and a control dependency without explicit
            // branching
            fact = createAssign(i, cond);
            fact += "\n";
            fact += createAssign(i, trueVal);
            fact += "\n";
            fact += createAssign(i, falseVal);
          }
          else if (VAArgInst *i = dyn_cast<VAArgInst>(&I)) {
            llvm_unreachable("unimplemented");
            // The pointer operand is the va_list?
            Value *ptr = i->getPointerOperand();
            createAssign(i, ptr);
          }
          else if (ExtractElementInst *i = dyn_cast<ExtractElementInst>(&I)) {
            // TODO: All vectors are considered to be the same (i.e., the index
            // of ExtractElement is ignored
            Value *vec = i->getVectorOperand();
            createAssign(i, vec);
          }
          else if (InsertElementInst *i = dyn_cast<InsertElementInst>(&I)) {
            // InsertElement takes a vector, index, and value and returns the
            // vector with the value at the index.
            // This makes the return data dependent on all three values
            assert(i->getNumOperands() == 3 && "insertelement w/o 3 operands");
            Value *v0 = i->getOperand(0);
            Value *v1 = i->getOperand(0);
            Value *v2 = i->getOperand(0);

            fact = createAssign(i, v0);
            fact += "\n";
            fact += createAssign(i, v1);
            fact += "\n";
            fact += createAssign(i, v2);
          }
          else if (ShuffleVectorInst *i = dyn_cast<ShuffleVectorInst>(&I)) {
            // A shufflevectorinst is required to have a constant vector
            // shuffle mask or have an undef shuffle mask.
            // TODO: The mask could be interpreted to determine if, for
            // example, the shuffle mask results in an identity operation. This
            // would reduce the data dependencies.
            // TODO: Likely need to handle undef values and constants being
            // assigned here
            Constant *mask = i->getMask();
            // TODO: Does the mask count as an operand or is it just the two
            // vectors?
            assert(i->getNumOperands() == 2 && "shufflevec w/o two operands");
            Value *vec1 = i->getOperand(0);
            Value *vec2 = i->getOperand(1);

            fact = createAssign(i, vec1);
            fact += "\n";
            fact += createAssign(i, vec2);
            // TODO: Does there need to be a data dependency to a constant?
            fact += "\n";
            fact += createAssign(i, mask);
          }
          else if (ExtractValueInst *i = dyn_cast<ExtractValueInst>(&I)) {
            // TODO: All extractions from structs/arrays are considered to be
            // the same: the index is ignored
            Value *agg = i->getAggregateOperand();
            fact = createAssign(i, agg);
          }
          else if (InsertValueInst *i = dyn_cast<InsertValueInst>(&I)) {
            // TODO: All insertions to structs/arrays are considered to be the
            // same: the index is ignored
            Value *agg = i->getAggregateOperand();
            fact = createAssign(i, agg);
          }
          else if (LandingPadInst *i = dyn_cast<LandingPadInst>(&I)) {
            // TODO: The landing pad instruction is dependent on the
            // personality function?
            Value *persFunc = i->getPersonalityFn();
            fact = createAssign(i, persFunc);
          }
          else if (isa<DbgDeclareInst>(&I)) {
            // Debug declare can be skipped: it is only metadata
            continue;
          }
          else if (isa<DbgValueInst>(&I)) {
            // Debug value can be skipped: it is only metadata
            continue;
          }
          else if (isa<DbgInfoIntrinsic>(&I)) {
            // What is this instruction?
            continue;
          }
          else if (MemSetInst *i = dyn_cast<MemSetInst>(&I)) {
            // memset is a store to the pointer operand of a certain length. It
            // has no return value
            // Destination address
            Value *dst = i->getRawDest();

            // Number of bytes to set. Unused
            //Value *lgnth = i->getLength();
            
            // Byte to be copied to address
            Value *val = i->getValue();
            // The two constants can be skipped over?
            //ConstantInt *algn = i->getAlignment();
            //ConstantInt *vol = i->getVolatileCst();

            // TODO: The length of memset is ignored.
            fact = createStore(dst, val, i);
          }
          else if (MemCpyInst *i = dyn_cast<MemCpyInst>(&I)) {
            Value *src = i->getRawSource();
            Value *dst = i->getRawDest();

            // TODO: the length is ignored
            fact = createMemCpy(dst, src);
          }
          else if (MemMoveInst *i = dyn_cast<MemMoveInst>(&I)) {
            Value *src = i->getRawSource();
            Value *dst = i->getRawDest();

            // TODO: the length is ignored
            fact = createMemCpy(dst, src);
          }
          //else if (MemTransferInst *i = dyn_cast<MemTransferInst>(&I)) {
          else if (isa<MemTransferInst>(&I)) {
            llvm_unreachable("memtransfer should have been handled");
          }
          else if (isa<MemIntrinsic>(&I)) {
            llvm_unreachable("meminstrinsic should have been handled");
          }
          else if (isa<VAStartInst>(&I)) {
            // va_start has no dependencies
            continue;
          }
          else if (isa<VAEndInst>(&I)) {
            // va_end has no dependencies
            continue;
          }
          else if (VACopyInst *i = dyn_cast<VACopyInst>(&I)) {
            // va_copy is just like memcpy
            Value *src = i->getSrc();
            Value *dst = i->getDest();
            fact = createMemCpy(dst, src);
          }
          else if (isa<IntrinsicInst>(&I)) {
            llvm_unreachable("instrinsic inst should have been handled");
          }
          else if (isa<BinaryOperator>(&I)) {
            // binary operation should have two operands
            assert(I.getNumOperands() == 2 && "BinaryOperator w/o 2 operands");
            Value *op0 = I.getOperand(0);
            Value *op1 = I.getOperand(1);
            // The result of the binary operator is data dependent on both its
            // operands
            fact = createAssign(&I, op0);
            fact += "\n";
            fact += createAssign(&I, op1);
          }

          assert(fact.size() && "fact not set");

          (*outFile) << "; " << I << '\n';
          (*outFile) << fact << '\n';
        }
      }
    }
    // save the ID map
    IDMap.useBitvectors = true;
    IDMap.dumpIDMapToModule(M);
    // TODO: This is just here to make sure the parse/dump code is working
    // properly
    std::map<Value *, std::string> parseMap =
      ValToStrDB::parseIDMapFromModule(M);
    for (auto i = parseMap.begin(), e = parseMap.end(); i != e; ++i) {
      Value *v = i->first;
      std::string s = i->second;
      std::string oldStrID = IDMap.saveAndGetID(v);
      std::string oldIntID = 
        Utils::to_const_bitvec(IDMap.saveAndGetIntID(oldStrID));
      assert(s == oldIntID && "IDMaps do not match up");
    }
    for (auto i = IDMap.IDMap.begin(), e = IDMap.IDMap.end(); i != e; ++i) {
      Value *v = i->first;
      auto f = parseMap.find(v);
      assert(f != parseMap.end() && "item not found in parse map");
      std::string s = f->second;
      std::string intIdStr = Utils::to_const_bitvec(IDMap.saveAndGetIntID(v));

      assert(s == intIdStr && "ID not saved to module");
    }

    DEBUG_MSG("Done\n");
    (*outFile) << "\n; End Facts\n";
    outFile->close();
    delete outFile;

    // Close the output file and clean it up

    // IR was modified (but only the metadata)
    return true;
  }
};

char ContextInsenPDG::ID = 0;
static RegisterPass<ContextInsenPDG> X("contextinsen-pdg",
            "Datalog based frontend for context insensitive program dependence" 
            " graph calculation",
            false,  // unmodified CFG
            true); // analysis pass
