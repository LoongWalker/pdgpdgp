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
 *
 * TODO:
 *    * Should a callsite  be dependent on its arguments? Currently, it is not
 */

#include "llvm/Pass.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/DerivedTypes.h"
//#include "llvm/IR/Module.h"
//#include "llvm/IR/Instructions.h"
//#include "llvm/Support/raw_ostream.h"
//#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/LLVMContext.h"

//#include "../ContextInsenAA/FactVisitor.h"
#include "ControlDependence.h"

#include "../utils/ValToStrDB.h"
#include "../utils/utils.h"
#define MK_DEBUG
#include "../utils/mk_debug.h"

#include <string>
#include <vector>
#include <fstream>

#include <z3.h>
#include <z3++.h>
#include <z3_api.h>
#include <z3_fixedpoint.h>

using namespace llvm;

// This size needs to be able to represent all the values used in the analysis.
// Increase it as necessary. If it gets too big, things seem to get pretty
// slow.
static const unsigned Z3_BV_SIZE = 16;


// Command line option. If this is true, then a points-to query will be
// inserted in the output file for each assertion.
static cl::opt<bool> 
    queryAssert("assert", 
	cl::desc("Add a query to the output file to slice on each assertion"),
	cl::init(false));

static cl::list<std::string>
    fwdSliceIds("fwd"
      , cl::desc("generate a smt2 file querying forward slice on the passed"
                 "instruction IDs.")
	    , cl::CommaSeparated);

cl::opt<std::string>
  z3BinLoc("z3"
      , cl::desc("Location of Z3 binary.")
      , cl::init(""));

cl::opt<bool>
	sliceMD("mdassert"
			, cl::desc("If true, z3 will be executed and instructions on the slice of " 
								 "an assertion will be tagged with metadata")
			, cl::init(false));

static cl::list<std::string>
  impactIds("impact"
            , cl::desc("execute Z3 and separately mark instructions which are"
                       " impacted/may-impact the list of provided instruction"
                       " IDs")
	          , cl::CommaSeparated);

// Returns true if the passed function should not be visited
static bool skipFunction(const Function *f) {
    // ignore indirect functions
    if (f == NULL)
      return false;
    std::string name = f->getName();

    if (name.substr(0, sizeof("__assert_fail") -1) == "__assert_fail") {
      return false;
    }

    if (name.substr(0, 8) == "__uClibc") {
      return true;
    }
    if (name.substr(0, sizeof("__check_suid") - 1) == "__check_suid") {
      return true;
    }
    if (name.substr(0, sizeof("__check_one_fd") - 1) == "__check_one_fd") {
      return true;
    }
    if (name.substr(0, sizeof("__syscall_") - 1) == "__syscall_") {
      return true;
    }
    if (name.substr(0, sizeof("getcwd") - 1) == "getcwd") {
      return true;
    }
    if (name.substr(0, sizeof("__libc_") - 1) == "__libc_") {
      return true;
    }
    if (name.substr(0, sizeof("getutid") - 1) == "getutid") {
      return true;
    }
    if (name.substr(0, sizeof("gnu_dev_makedev165") - 1) == "gnu_dev_makedev165") {
      return true;
    }
    if (name.substr(0, sizeof("__setutent") - 1) == "__setutent") {
      return true;
    }
    if (name.substr(0, sizeof("endutent") - 1) == "endutent") {
      return true;
    }
    if (name.substr(0, sizeof("__getutent") - 1) == "__getutent") {
      return true;
    }
    if (name.substr(0, sizeof("pututline") - 1) == "pututline") {
      return true;
    }
    if (name.substr(0, sizeof("utmpname") - 1) == "utmpname") {
      return true;
    }
    if (name.substr(0, sizeof("__stdio_READ") - 1) == "__stdio_READ") {
      return true;
    }
    if (name.substr(0, sizeof("__stdio_WRITE") - 1) == "__stdio_WRITE") {
      return true;
    }
    if (name.substr(0, sizeof("exit") - 1) == "exit") {
      return true;
    }
    if (name.substr(0, sizeof("_fpmaxtostr") - 1) == "_fpmaxtostr") {
      return true;
    }
    if (name.substr(0, sizeof("pthread_once") - 1) == "pthread_once") {
      return true;
    }
    if (name.substr(0, sizeof("__close_fds") - 1) == "__close_fds") {
      return true;
    }
    if (name.substr(0, sizeof("sendfile") - 1) == "sendfile") {
      return true;
    }
    if (name.substr(0, sizeof("_read_file") - 1) == "_read_file") {
      return true;
    }
    if (name.substr(0, sizeof("_write_file") - 1) == "_write_file") {
      return true;
    }
    if (name.substr(0, sizeof("_open_symbolic") - 1) == "_open_symbolic") {
      return true;
    }
    if (name.substr(0, sizeof("__klee_model_creat") - 1) == "__klee_model_creat") {
      return true;
    }
    if (name.substr(0, sizeof("mmap") - 1) == "mmap") {
      return true;
    }
    if (name.substr(0, sizeof("_scatter_read") - 1) == "_scatter_read") {
      return true;
    }
    if (name.substr(0, sizeof("_is_blocking") - 1) == "_is_blocking") {
      return true;
    }
    if (name.substr(0, sizeof("_clean_read") - 1) == "_clean_read") {
      return true;
    }
    if (name.substr(0, sizeof("_gather_write") - 1) == "_gather_write") {
      return true;
    }
    if (name.substr(0, sizeof("_clean_write") - 1) == "_clean_write") {
      return true;
    }
    if (name.substr(0, sizeof("__klee_model_close") - 1) == "__klee_model_close") {
      return true;
    }
    if (name.substr(0, sizeof("__klee") - 1) == "__klee") {
      return true;
    }
    if (name.substr(0, sizeof("_") - 1) == "_") {
      return true;
    }
    if (name.substr(0, sizeof("__") - 1) == "__") {
      return true;
    }
    if (name.substr(0, sizeof("_open_symbolic") - 1) == "_open_symbolic") {
      return true;
    }

    return false;
  }

struct ContextInsenDynPDG : ModulePass {
  static char ID;
  ValToStrDB IDMap;
  // Vector populated with all the __assert_fail calls found during the
  // traversal of every instruction.
  //
  // The vector should only contain CallInsts or InvokeInsts
  std::vector<Instruction *> assertCalls;

  

  ContextInsenDynPDG() : ModulePass(ID) { }

  void addSpec(raw_fd_ostream &f) {
    std::string unsigned_size_bits = std::to_string(sizeof(unsigned) * 8);
    f << "(set-option :fixedpoint.engine datalog)\n"
      << "; This sort is used to define all relations. It is the size of an\n"
      << "; unsigned on the target machine.\n"
      << "(define-sort s () (_ BitVec " << unsigned_size_bits << "))\n"
      << "\n"
      << "; Data dependency (assign to from) => (to<--from)\n"
      << "(declare-rel assign (s s))\n"
      << "; Control dependency (control-dep to from) => (to<--from)\n"
      << "(declare-rel control-dep (s s))\n"
      << "; A program dependency is either a control or data dependency\n"
      << "(declare-rel prog-dep (s s))\n"
      << "; points-to relation: this is relation contains any two values\n"
      << "; (regardless of if they are pointers) if they have a common\n"
      << "; ancestor in the data dependency graph (i.e. backwards reachable)\n"
      << "(declare-rel points-to (s s))\n"
      << '\n'
      << "(declare-var to s)\n"
      << "(declare-var from s)\n"
      << "(declare-var pred s)\n"
      << '\n';

    f << "; A program dependency is either a control or data dependency\n"
      << "; This relation defines the program dependency graph\n"
      << "(rule (=> (control-dep to from) (prog-dep to from)))\n"
      << "(rule (=> (assign to from) (prog-dep to from)))\n"
      << "; Recusrive step: create the transitive closure of program\n"
      << "; dependencies\n"
      << "(rule (=> (and (prog-dep to from) (prog-dep from pred))\n"
      << "\t(prog-dep to pred)))\n"
      << "\n"
      << "; The data dependency graph can be used to query if two pointers\n"
      << "; (or, any two values) share a common data dependency\n"
      << "(rule (=> (assign to from) (points-to to from)))\n"
      << "\n"
      << "; A pointer points to the transitive closure of its assignments\n"
      << "(rule (=> (and (assign to from) (points-to from pred))\n"
      << "\t(points-to to pred)))\n"
      << '\n';
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
    assert(to->getType()->isPointerTy() && "to value that is not a pointer");

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
    assert(from->getType()->isPointerTy() 
        && "from value that is not a pointer");

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
    assert(from->getType()->isPointerTy() 
        && "from value that is not a pointer");

    if (ConstantExpr *ce = dyn_cast<ConstantExpr>(from)) {
      from = ValToStrDB::getConstExprUse(ce);
    }

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

  // Create a rule:
  // call(callSite, callee)
  // This means that the callSite calls the passed pointer to a callee
  std::string createCall(Value *callSite, Value *callee) {
    assert(callSite && "NULL passed");
    assert(callee && "NULL passed");

    // Attempt to convert to and from to values which are handled
    std::string csStr = IDMap.saveAndGetID(callSite);
    std::string calleeStr = IDMap.saveAndGetID(callee);

    return createCall(csStr, calleeStr);

  }

  std::string createCall(std::string cs, std::string callee) {
    assert(cs.size() && "empty callsite string passed");
    assert(callee.size() && "empty callee string passed");
    std::string csStr = Utils::to_const_bitvec(IDMap.saveAndGetIntID(cs));
    std::string calleeStr 
      = Utils::to_const_bitvec(IDMap.saveAndGetIntID(callee));

    std::string ret;
    ret = "(rule (call " + csStr + ' ' + calleeStr + "))";
    return ret;
  }

  // returns true if the passed function type has the same types as the passed
  // vector of types. Order matters in the passed vector. This assumes that the
  // number of types in the passed vector and in the parameters of the passed
  // function are the same. Otherwise, this function will crash
  bool paramsMatch(FunctionType *fTy, std::vector<Type *> const tys) {
    assert(fTy->getNumParams() == tys.size() 
        && "number of arguments in function does not match vector");
    unsigned pos = 0;
    for (auto pi = fTy->param_begin(), pe = fTy->param_end(); pi != pe; 
        ++pi) {
      Type *t = *pi;
      if (t != tys[pos]) {
        return false;
      }
      // keep track of which argument we are on
      pos++;
    }
    return true;
  }

  // Creates a conditional assignment rule:
  //
  // (rule (=> (points-to toPtr fromPtr) (assign to fromStr)))
  //
  // Or, to is assigned fromStr (to <-- fromStr) if toPtr points to fromPtr
  // (toPtr --> fromPtr)
  std::string createCondAssign(Value *toPtr, Value* fromPtr, 
      Value* to, std::string fromStr) {
    assert(toPtr && "NULL passed");
    assert(fromPtr && "NULL passed");
    assert(to && "NULL passed");
    assert(fromStr.size() && "empty string passed");
    std::string toPtrStr = IDMap.saveAndGetID(toPtr);
    std::string fromPtrStr = IDMap.saveAndGetID(fromPtr);
    std::string toStr = IDMap.saveAndGetID(to);

    return createCondAssign(toPtrStr, fromPtrStr, toStr, fromStr);
  }

  std::string createCondAssign(Value *toPtr, Value* fromPtr, 
      Value* to, Value *from) {
    assert(toPtr && "NULL passed");
    assert(fromPtr && "NULL passed");
    assert(to && "NULL passed");
    assert(from && "NULL passed");

    std::string toPtrStr = IDMap.saveAndGetID(toPtr);
    std::string fromPtrStr = IDMap.saveAndGetID(fromPtr);
    std::string toStr = IDMap.saveAndGetID(to);
    std::string fromStr = IDMap.saveAndGetID(from);

    return createCondAssign(toPtrStr, fromPtrStr, toStr, fromStr);
  }

  std::string createCondAssign(std::string toPtr, std::string fromPtr,
      std::string toStr, std::string fromStr) {
    assert(toPtr.size() && "empty string passed");
    assert(fromPtr.size() && "empty string passed");
    assert(toStr.size() && "empty string passed");
    assert(fromStr.size() && "empty string passed");

    // assign string: (assign toStr fromStr)
    std::string assign = createAssign(toStr, fromStr);
    // cond string: (points-to toPtrStr fromPtrStr)
    std::string cond = createPointsTo(toPtr, fromPtr);

    // both createPointsTo and createAssign surround the result in a (rule ):
    // we do not need that here
    assign = removeRule(assign);
    cond = removeRule(cond);

    return "(rule (=> " + cond + ' ' + assign + "))";
  }

  // Create a rule: (points-to to from)
  //
  // Converts to bitvectors
  std::string createPointsTo(std::string to, std::string from) {
    assert(to.size() && "empty string passed");
    assert(from.size() && "empty string passed");

    to = Utils::to_const_bitvec(IDMap.saveAndGetIntID(to));
    from = Utils::to_const_bitvec(IDMap.saveAndGetIntID(from));

    return "(rule (points-to " + to + ' ' + from + "))";
  }


  // Given a string: (rule (...)) remove the "(rule ) and the last paren
  std::string removeRule(std::string s) {
    assert(s.size() && "emptry string passed");
    std::string ret = s;
    // Remove the rule:
    assert(s.substr(0, 7) == std::string("(rule (" )
        && "string does not start with (rule (");
    ret = s.substr(6, std::string::npos);

    // Remove the final paren
    assert(ret.back() == ')' && "string does not end with )");
    ret = ret.substr(0, ret.size() - 1);

    return ret;
  }

  // Given the passed callsite, return the matching set of functions which
  // could be called from the callsite. 
  // If the called value is a literal function (i.e., not a function pointer)
  // then the result will be a vector of size one containing this value.
  //
  // Otherwise, the return will be the set of all functions in the module which
  // have the same number of arguments and the same type of arguments.
  //
  // If no such functions are found, an empty vector is returned
  std::vector<Function *> getMatchingFunctions(CallSite cs) {
    std::vector<Function *> ret;
    Function *callee = cs.getCalledFunction();
    if (callee != NULL) {
      // CallSite calls a literal function (non-function pointer)
      ret.push_back(callee);
      assert(ret.size());
      return ret;
    }
    // Otherwise, the function is calling a function pointer
    Value *called = cs.getCalledValue();
    assert(called && "function calling NULL");

    Instruction *csInst = cs.getInstruction();
    Module *M = csInst->getParent()->getParent()->getParent();
    // Collect the arguments used in the callsite
    std::vector<Type*> csArgTypes;

    // If there are no callsite arguments, then we are searching for a
    // function which similarly has no arguments
    for (size_t i = 0; i < cs.arg_size(); ++i) {
      Value *a = cs.getArgument(i);
      csArgTypes.push_back(a->getType());
    }
    // Return type of the function/callsite
    Type *csRetTy = cs.getInstruction()->getType();
    
    // Iterate over each function and find those which match the signature of
    // the callsite
    for (auto fi = M->begin(), fe = M->end(); fi != fe; ++fi) {
      Function &f = *fi;
      FunctionType *fTy = f.getFunctionType();
      //assert(!fTy->isVarArg() && "var-arg functions unhandled");
      if (fTy->isVarArg()) {
        errs() << "[WARNING] Var-arg function call: arguments are NOT "
               << "followed in dependency graph (loss of precision)\n"
               << f << '\n';
      }
      // If the function has no arguments and we are looking for an argument
      // with no functions then we are good to go
      
      // Check if the return types match
      if (csRetTy != fTy->getReturnType()) {
        continue;
      }
      // Check if the function has the same number of arguments
      if (fTy->getNumParams() != csArgTypes.size()) {
        continue;
      }
      // Check if the type of each argument matches
      if (!paramsMatch(fTy, csArgTypes)) {
        continue;
      }
      ret.push_back(&f);
    }

    return ret;
  }

  std::string handleCallSite(CallSite I) {
    std::string ret = "";
    DEBUG_MSG("Visiting CallSite: " << *(I.getInstruction()) << "\n");
    DEBUG_MSG("\tType? " << *(I.getType()) << '\n');

    //Function *callee = I.getCalledFunction();
    //assert(callee != NULL && "Calling indirect function");
    Value *callee = I.getCalledValue();
    assert(callee && "calling NULL value");

    // Get the ID of the callsite instruction
    Instruction *csInst = I.getInstruction();

    // TODO: Should the call instruction be dependent on its arguments?

    // First, create a fact that this call site calls the passed pointer
    // The call graph edges are not explicitly recorded, we simply track the
    // pointer relations
    //ret += createCall(cs, callee);
    //ret += '\n';

    // Next, find potential functions which could be called by this
    // callsite. These are functions which have the same number of arguments
    // and the same type of arguments.
    //std::vector<Function *> funcs = getMatchingFunctions(csInst);
    std::vector<Function *> funcs = getMatchingFunctions(I);
    assert(funcs.size() && "no matching functions for callsite");
    DEBUG_MSG("\tFound " << funcs.size() << " matching function(s)\n");

    // For each matching function, create a conditional points-to edge to the
    // return of the function based on whether or not the pointer aliases to
    // the function
    for (auto f : funcs) {
      StringRef funcName = f->getName();
      assert(funcName.size() && "function w/o name");

      // Create a conditional assignment from the return of the function to
      // the call site
      // We only need to find potential callsites if the callsite is unknown
      // (i.e., the call is using a function pointer)
      std::string funcRetName = getFuncReturnName(funcName);
      if (I.getCalledFunction() == NULL) {
        ret += "; Function return\n";
        ret += createCondAssign(callee, f, csInst, funcRetName);
        ret += '\n';
        ret += "; Function arguments\n";
      }
      else {
        // just create a non conditional assignment to the callee from the
        // function return
        ret += "; Function return\n";
        ret += createAssign(IDMap.saveAndGetID(csInst), funcRetName);
        ret += '\n';
        ret += "; Function arguments\n";
      }

      // Create a conditional assignment from the callsite argument to the
      // function's arguments
      for (auto i = f->arg_begin(), e = f->arg_end(); i != e; ++i) {
        Argument &a = *i;

        // Get an ID to the operand used in the caller
        Value *callerOp = I.getArgument(a.getArgNo());
        assert(callerOp && "argument not found on caller");

        // Link the function argument to the callsite argument
        DEBUG_MSG("\tLinking function arg to callsite arg\n");
        //std::string fact = createAssign(&a, fromOp);
        if (I.getCalledFunction() == NULL) {
          std::string fact = createCondAssign(callee, f, &a, callerOp);
          ret += fact;
          ret += "\n";
        }
        else {
          std::string fact = createAssign(&a, callerOp);
          ret += fact;
          ret += "\n";
        }
      } // for (auto i = f->arg_begin() ... )
    } // for (auto f : funcs)

    DEBUG_MSG("Finished callsite\n");
    // None of these functions which return facts have newlines at the end
    assert(ret.size() && "ret not set");
    while (ret.back() == '\n') {
      ret = ret.substr(0, ret.size() - 1);
    }
    return ret;


    // Create an alias link from the return instruction to the return of the
    // function
    // Each function has a node for its return value (see visitReturnInst())
    //std::string funcRetName = getFuncReturnName(funcName);
    // Create an assignment to the CallSite (the return) to the return of the
    // function.
    //ret += createAssign(IDMap.saveAndGetID(cs), funcRetName);

    //DEBUG_MSG("\tHandling callsite arguments\n");

    // Callsite arguments are handled for each function after every instruction
    // is iterated over (it can also be done before).

#if 0
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
#endif
  }

  // Build the Z3 context and fixedpoint-solver with the PDG constraints
  // generated by the passed program.
  //
  // It is assumed that the passed ctx and Z3_fixedpoint have been initialized:
  // only additional relations/rules will be added
  void getPDGConstraints(Module &M, z3::context &ctx, Z3_fixedpoint &zfp) {

    // Add relations
    //addDataDepRel(ctx, zfp);
  }

  virtual bool runOnModule(Module &M) {
    DEBUG_MSG_RED("Starting context insensitive PDG pass\n");

    // Use the name of the module as the filename
    std::string modName = M.getModuleIdentifier();
    assert(modName.size() && "Module ID has size zero");
    std::string path;
    path = modName + ".smt2";
    assert(path.size() && "empty output file path");
    DEBUG_MSG("[DEBUG] smt2 filepath: " << path << '\n');

		checkCommandLineFlags();

    // Initialize the solver
    z3::config cfg;
    //Z3_set_param_value(cfg, "DL_DEFAULT_RELATION", "smt_relation2");
    z3::context ctx(cfg);
    Z3_fixedpoint zfp = Z3_mk_fixedpoint(ctx);
    Z3_fixedpoint_inc_ref(ctx, zfp);
    z3::params params(ctx);
    params.set("engine", ctx.str_symbol("datalog"));
    params.set("datalog.default_table", ctx.str_symbol("hashtable"));
    params.set("datalog.magic_sets_for_queries", true);

    getPDGConstraints(M, ctx, zfp);

    // Attempt to open a stream to the passed path, crash on failure.
    std::error_code ec;
    // Open file in text mode
    raw_fd_ostream *outFile = new raw_fd_ostream(path.c_str(), ec
        , sys::fs::OpenFlags::F_Text);
    //if (!ec.empty()) {
    if (ec) {
      errs() << "[ERROR] Unable to open file " << path << ": " << ec.message()
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
      // If the function has no body (externally defined) then skip it
      if (f.begin() == f.end()) {
        continue;
      }
      // If the function is on the list of functions to skip, then skip it.
      if (skipFunction(&f)) {
        continue;
      }
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
            // Keep track of assert calls incase we need
            // to make a query on them (-assert option)
            Function *f = i->getCalledFunction();
            if (f != NULL) {
              if (f->getName() == "__assert_fail") {
                assertCalls.push_back(i);
                // skip assert calls
                continue;
              }
            }
            
            // This point is reached if the call is not to __assert_fail
            CallSite cs = CallSite(i);
            // If the function has no matching functions in the file, skip it
            if (getMatchingFunctions(cs).size() == 0) {
              continue;
            }
            fact = handleCallSite(cs);

          }
          else if (InvokeInst *i = dyn_cast<InvokeInst>(&I)) {
            // Keep track of assert calls incase we need
            // to make a query on them (-assert option)
            Function *f = i->getCalledFunction();
            if (f != NULL) {
              if (f->getName() == "__assert_fail") {
                assertCalls.push_back(i);
                // skip assert calls
                continue;
              }
            }
            // This point is reached if the call is not to __assert_fail
            CallSite cs = CallSite(i);
            // If the function has no matching functions in the file, skip it
            if (getMatchingFunctions(cs).size() == 0) {
              continue;
            }
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
          else if (PHINode *pn = dyn_cast<PHINode>(&I)) {
            // The result of a phinode is dependent on all the possible values
            // in the instruciton
            for (size_t i = 0; i < pn->getNumIncomingValues(); ++i) {
              Value *v = pn->getIncomingValue(i);
              fact += createAssign(&I, v);
              fact += "\n";
            }
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
            // TODO: what are the dependenciers for a landingpad?

            // TODO: The landing pad instruction is dependent on the
            // personality function?
            //Value *persFunc = i->getPersonalityFn();
            //fact = createAssign(i, persFunc);
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
          else if (isa<UnreachableInst>(&I)) {
            // unreachable has no dependencies
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
          else {
            errs() << "[ERROR]: Unhandled instruction: " << I << '\n';
            exit(EXIT_FAILURE);
          }

          DEBUG_MSG("Instruction: " << I << "\n");
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

    ///////////// Add queries to the output file
    // Add a query for each assertion
    if (queryAssert) {
      for (size_t i = 0; i < assertCalls.size(); ++i) {
        Instruction *inst = assertCalls[i];
        writeUniversalQuery(inst, "q" + std::to_string(i), outFile);
      }
    }

    // Add forward slice quieries
    if (fwdSliceIds.size()) {
      int count = 0;
      for (std::string s : fwdSliceIds) {
        std::string varName = "fw" + std::to_string(count);
        writeFwdSlice(s, varName, outFile);
        count++;
      }
    }
    ///////////// End additions of queries


    DEBUG_MSG("Done\n");
    (*outFile) << "\n; End Facts\n";

    // Close the output file and clean it up
    outFile->close();
    delete outFile;

    ///////////// Query the SMT2 file and add metadata
    // Note: this must be done without any additional queries are added to the
    // file otherwise their outputs will get mixed up
		if (sliceMD) {
			markAsserts(M, path, assertCalls);
		}

    if (impactIds.size()) {
      addImpactedAndMayImpact(impactIds, M, path);
    }
    ///////////// End processing Z3 output



    // IR was modified (but only the metadata)
    return true;
  }

  // Write a query asking: "What is program dependent to the passed instruction?" VarName
  // is the name of the Z3 variable to use in the universal quantification.
  // The variable will first be defined and then used in the query.
  void writeUniversalQuery(Instruction *i, std::string varName, 
      raw_fd_ostream *os) {

    unsigned instId = IDMap.saveAndGetIntID(i);
    std::string idStr = Utils::to_const_bitvec(instId);

    writeUniversalQuery(idStr, varName, os);

  }

  void writeUniversalQuery(std::string idStr, std::string varName
      , raw_fd_ostream *os) {
    // Write a definition for the variable
    // s is the sort of all the IDs used in Z3
    (*os) << "(declare-var " + varName + " s)\n";

    // Write the query
    (*os) << "(query (prog-dep " << idStr << " " << varName 
          << ") :print-answer true)\n";
  }

  // Write a query asking: "What is the forward slice of the passed ID"
  // This is the reverse of writeUniversalQuery() (it does a backward slice)
  void writeFwdSlice(std::string instId, std::string varName,
      raw_fd_ostream *os) {
    // Write a definition for the variable
    // s is the sort of all the IDs used in Z3
    (*os) << "(declare-var " + varName + " s)\n";

    // Write the query
    (*os) << "(query (prog-dep " << varName << " " << instId
          << ") :print-answer true)\n";
    return;
  }

  // Assuming that smt2Path is the path to a .smt2 file with a
  // query in it, run Z3 on smt2Path an mark any nodes in the
  // output with metadata mdName.
  void markZ3Output(Module &M, std::string smt2Path
                   , std::string mdName) {
    DEBUG_MSG("[DEBUG] Marking Z3 output, md name:" << mdName << '\n');
		assert(z3BinLoc.size() && "z3 path not set");
		assert(smt2Path.size() && ".smt2 path not set");
		std::string z3OutputName = "z3_out.tmp";

		std::string cmd;
		cmd = z3BinLoc
				 + " " + smt2Path
				 + " | tail -n +2" // trim first line
				 + " | sed '/sat/d'" // remove results of query
				 + " | sed 's/^(or //g'" // remove "(or" on first line
				 + " | sed 's/^[ \t]*//'" // remove leading whitespace
				 + " | sed 's/(= (:var 0) //g'"  // remove leading (= 
				 + " | sed 's/)//g'" // remove trailing paren
				 + " | sed 's/#x//g'" // remove leading #x
         + " | sed 's/ /\\n/g'" // split multiple numbers on single line
				 + "  >" + z3OutputName; // save in temporary file
		int retCode = system(cmd.c_str());
		if (retCode != 0) {
			errs() << "[ERROR] error running z3/parsing output: " << retCode << '\n';
			exit(EXIT_FAILURE);
		}
		// z3_out.tmp contains one hex string per-line with leading zeros
		// Open the output file and parse each line to an integer
		//std::string ec;
		std::error_code ec;
    raw_fd_ostream *z3Out = new raw_fd_ostream(smt2Path.c_str(), ec
        , sys::fs::OpenFlags::F_Text);
    //if (!ec.empty()) {
    if (ec) {
      errs() << "[ERROR] Unable to open file: " << smt2Path << ": " << ec.message()
             << '\n';
      exit(EXIT_FAILURE);
    }

		std::ifstream tmpFile(z3OutputName);
		for (std::string line; getline(tmpFile, line); ) { 
			// Convert from hex to decimal
			DEBUG_MSG("  line: " << line << '\n');
			unsigned int cur = std::stoul(line, nullptr, 16);
			// Convert to string to lookup in map
			//std::string curStr = std::to_string(cur);
			//Value *v = IDMap.getValueOrNULL(line);
			Value *v = IDMap.getValueOrNULL(cur);
			if (v == NULL) {
				// some of the items in the z3 file are merge nodes. They do not have
				// an explicit representation in the LLVM file
				continue;
			}
			if (Instruction *i = dyn_cast<Instruction>(v)) {
				// Metadata is only inserted on instructions
				LLVMContext &C = M.getContext();
				//Value* elts[] = { ConstantInt::get(C, APInt(1, 1)) };
        Metadata *elts[] = { ValueAsMetadata::get(ConstantInt::get(C, APInt(1, 1))) };
				MDNode* md_node = MDNode::get(C, elts);
				i->setMetadata(mdName, md_node);
			}
		}
		// Close and cleanup file
		z3Out->close();
		delete z3Out;
  }

  // Attempt to copy fromPath to toPath.
  //
  // Returns false on error, otherwise true.
  static bool copyFiles(std::string fromPath, std::string toPath) {
    DEBUG_MSG("copyFiles: to: " << toPath << "\tfrom: " << fromPath << '\n');

    std::ifstream from(fromPath, std::ios::binary);
    if (!from) {
      errs() << "[ERROR] copyFiles: unable to open from file:" 
             << fromPath << ", aborting\n";
      return false;
    }
    std::ofstream to(toPath
        , std::ofstream::trunc | std::ios::binary);
    if (!to) {
      errs() << "[ERROR] copyFiles: unable to open to file:" 
             << toPath << ", aborting\n";
      return false;
    }
    to << from.rdbuf();
    return true;
  }

  // Remove .smt2 at the end of path if possible. Otherwise, just return path.
  std::string removeSmt2Extension(std::string path) {
    // Try to remove .smt2 prefix if it exists
    std::string basePath = path;
    auto basePathIter = basePath.find(".smt2");
    if (basePathIter != std::string::npos) {
      basePath.erase(basePathIter, 5);
    }
    return basePath;
  }

  // Given the construction of the PDG at smt2path, add metadata to each
  // instruction on the slice of the assertion. This assumes there are no
  // queries added to the smt2 file.
	void markAsserts(Module &M, std::string smt2Path
      , std::vector<Instruction *> assertCalls) {
    std::string path = removeSmt2Extension(smt2Path) + "-mdassert.smt2";
    int ret = copyFiles(smt2Path, path);
    if (!ret) {
      errs() << "[ERROR] unable to copy smt2 file for assertions.\n"
             << "aborting writing assertion metadata\n";

      return;
    }

    std::error_code ec;
    raw_fd_ostream *smt2File = new raw_fd_ostream(path.c_str(), ec
        , sys::fs::OpenFlags::F_Text | sys::fs::OpenFlags::F_Append);

    if (ec) {
      errs() << "[ERROR] error opening assert smt2 file: " << ec.message() 
             << "\nAborting adding assertion slice metadata\n";
      return;
    }

    // Add queries for each assertion
    for (size_t i = 0; i < assertCalls.size(); ++i) {
      Instruction *inst = assertCalls[i];
      writeUniversalQuery(inst, "q" + std::to_string(i), smt2File);
    }

    // Cleanup everything and ensure the file is flushed
    smt2File->close();
    delete smt2File;

    // Run Z3 and attach the output
    markZ3Output(M, smt2Path, "AssertSlice");
    //DEBUG_MSG("[DEBUG] Marking assertions");
		//assert(z3BinLoc.size() && "z3 path not set");
		//assert(smt2Path.size() && ".smt2 path not set");
		//std::string z3OutputName = "z3_out.tmp";

		//std::string cmd;
		//cmd = z3BinLoc
		//		 + " " + smt2Path
		//		 + " | tail -n +2" // trim first line
		//		 + " | sed '/sat/d'" // remove results of query
		//		 + " | sed 's/^(or //g'" // remove "(or" on first line
		//		 + " | sed 's/^[ \t]*//'" // remove leading whitespace
		//		 + " | sed 's/(= (:var 0) //g'"  // remove leading (= 
		//		 + " | sed 's/)//g'" // remove trailing paren
		//		 + " | sed 's/#x//g'" // remove leading #x
		//		 + "  >" + z3OutputName; // save in temporary file
		//int retCode = system(cmd.c_str());
		//if (retCode != 0) {
		//	errs() << "[ERROR] error running z3/parsing output: " << retCode << '\n';
		//	exit(EXIT_FAILURE);
		//}
		//// z3_out.tmp contains one hex string per-line with leading zeros
		//// Open the output file and parse each line to an integer
		////std::string ec;
		//std::error_code ec;
    //raw_fd_ostream *z3Out = new raw_fd_ostream(smt2Path.c_str(), ec
    //    , sys::fs::OpenFlags::F_Text);
    ////if (!ec.empty()) {
    //if (ec) {
    //  errs() << "[ERROR] Unable to open file: " << smt2Path << ": " << ec.message()
    //         << '\n';
    //  exit(EXIT_FAILURE);
    //}

		//std::ifstream tmpFile(z3OutputName);
		//for (std::string line; getline(tmpFile, line); ) { 
		//	// Convert from hex to decimal
		//	DEBUG_MSG("  line: " << line << '\n');
		//	unsigned int cur = std::stoul(line, nullptr, 16);
		//	// Convert to string to lookup in map
		//	//std::string curStr = std::to_string(cur);
		//	//Value *v = IDMap.getValueOrNULL(line);
		//	Value *v = IDMap.getValueOrNULL(cur);
		//	if (v == NULL) {
		//		// some of the items in the z3 file are merge nodes. They do not have
		//		// an explicit representation in the LLVM file
		//		continue;
		//	}
		//	if (Instruction *i = dyn_cast<Instruction>(v)) {
		//		// Metadata is only inserted on instructions
		//		LLVMContext &C = M.getContext();
		//		//Value* elts[] = { ConstantInt::get(C, APInt(1, 1)) };
    //    Metadata *elts[] = { ValueAsMetadata::get(ConstantInt::get(C, APInt(1, 1))) };
		//		MDNode* md_node = MDNode::get(C, elts);
		//		i->setMetadata("AssertSlice", md_node);
		//	}
		//}
		//// Close and cleanup file
		//z3Out->close();
		//delete z3Out;
	}

  // Mark all the instructions on the forward slice of instructions in Ids as
  // impacted ("Impacted" metadata), and all those on the backward slice as
  // MayImpact ("MayImpact" metadata)
  void addImpactedAndMayImpact(std::vector<std::string> ids, Module &M, std::string path) {
    DEBUG_MSG("[DEBUG] Adding impact IDs\n");

    // we make a copy of the original smt2 file for the forward and backward
    // impact queries so we can distinguish between the two.
    
    std::string basePath = removeSmt2Extension(path);
    DEBUG_MSG("Base path:" << basePath << '\n');

    std::string fwdImpactPath = basePath + "-fwdimp.smt2";
    std::string bwdImpactPath = basePath + "-bwdimp.smt2";
    bool suc;
    suc = copyFiles(path, bwdImpactPath);
    if (!suc) {
      errs() << "[ERROR] unable to copy backward impact file, aborting adding "
             << "impact metadata\n";
      return;
    }
    suc = copyFiles(path, fwdImpactPath);
    if (!suc) {
      errs() << "[ERROR] unable to copy backward impact file, aborting adding "
             << "impact metadata\n";
      return;
    }

    // Open the copies
    std::error_code ec;
    raw_fd_ostream *fwdFile = new raw_fd_ostream(fwdImpactPath.c_str(), ec
        , sys::fs::OpenFlags::F_Text | sys::fs::OpenFlags::F_Append);
    if (ec) {
      errs() << "[ERROR] addImpactAndMayImpact: unable to open fwd copy "
             << ec.message() << "\n";
      delete fwdFile;
      return;
    }

    raw_fd_ostream *bwdFile = new raw_fd_ostream(bwdImpactPath.c_str(), ec
        , sys::fs::OpenFlags::F_Text | sys::fs::OpenFlags::F_Append);
    if (ec) {
      errs() << "[ERROR] addImpactAndMayImpact: unable to open bwd copy "
             << ec.message() << "\n";
      fwdFile->close();
      delete fwdFile;
      delete bwdFile;
      return;
    }
    DEBUG_MSG("opened forward and backward copies\n");

    // Next add the backward and forward slice queries
    int count = 0; // counter used to unique variable names
    for (std::string id : ids) {
      DEBUG_MSG("writing impact queries\n");
      // Since they are in different files, we can use the same variable name
      // for the query.
      std::string varName = "impact" + std::to_string(count);
      writeFwdSlice(id, varName, fwdFile);
      writeUniversalQuery(id, varName, bwdFile);
      count++;
    }

    // Cleanup, we're done writing to the files. We need to do this so that
    // when Z3 opens them the buffers a flushed(? probably).
    fwdFile->close();
    delete fwdFile;
    bwdFile->close();
    delete bwdFile;

    // Run Z3 and attach metadata to the output file
    DEBUG_MSG("attaching forward impact metadata\n");
    markZ3Output(M, fwdImpactPath, "Impacted");
    DEBUG_MSG("attaching backward impact metadata\n");
    markZ3Output(M, bwdImpactPath, "MayImpact");
  }


	// This will crash if any of the flags are inconsistent
	void checkCommandLineFlags() {
    // Other command line flags adding queries to the SMT2 file
    // cause issues with impactIds. This could be solved by
    // copying the SMT2 file for each of the options.
    if (impactIds.size() && (fwdSliceIds.size() || queryAssert)){
      errs() << "[ERROR] -impact cannot be used with -fwd, or -assert" 
             << "\n";
      exit(EXIT_FAILURE);
    }
    if (impactIds.size() && (fwdSliceIds.size() || queryAssert)){
      errs() << "[ERROR] -mdassert cannot be used with -fwd, -assert" 
             << "\n";
      exit(EXIT_FAILURE);
    }
    if (impactIds.size() && !z3BinLoc.size()) {
			errs() << "[ERROR] Z3 binary must be provided with -impact (-z3)\n";
      exit(EXIT_FAILURE);
    }
		if (sliceMD && !z3BinLoc.size()) {
			errs() << "[ERROR] Z3 binary must be provided with -mdassert (-z3)\n";
			exit(EXIT_FAILURE);
		}
    //if (sliceMD && !queryAssert) {
    //  // adding slice metadata requires that slice queries are added
    //  queryAssert = true;
    //}
	}
};

char ContextInsenDynPDG::ID = 0;
static RegisterPass<ContextInsenDynPDG> X("contextinsen-dynpdg",
            "Datalog based frontend for dynamic context insensitive program "
            "dependence graph calculation",
            false,  // unmodified CFG
            true); // analysis pass
