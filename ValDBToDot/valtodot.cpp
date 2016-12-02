/*
 * Author: Markus Kusano
 *
 * Given a Bitcode file which is an embedded ValToStrDB this will dump the
 * contents of the database to DOT format.
 *
 * Currently this only supports dataabases with keys stored as hex bitvector
 * constants  (i.e., #x0000001a)
 */

#include "llvm/Pass.h"
//#include "llvm/IR/Instruction.h"
//#include "llvm/IR/Module.h"
//#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
//#include "llvm/Support/CommandLine.h"

#include "../utils/utils.h"
#include "../utils/ValToStrDB.h"
//#define MK_DEBUG
#include "../utils/mk_debug.h"

#include <string>

using namespace llvm;

struct ValDBToDot : ModulePass {
  static char ID;
  ValToStrDB IDMap;

  ValDBToDot() : ModulePass(ID) { }

  // Return s but with its bit vector constant tag removed (i.e., #x)
  std::string rmBitvecConst(std::string s) {
    assert(s.substr(0,2) == "#x"
        && "string w/o bitvector constant");
    return s.substr(2, std::string::npos);
  }

  // Return s but with its leading zeros removed
  std::string rmLeadingZeros(std::string s) {
    if (s.size() == 0) {
      return s;
    }

    DEBUG_MSG("triming leading zeros:\n\tBefore: " << s << '\n');
    size_t nz = s.find_first_not_of("0");
    if (nz == std::string::npos) {
      // If no matching characters are found then the entire string is zeros.
      // Just return one of them
      return std::string("0");
    }
    std::string ret = s.substr(nz, std::string::npos);
    DEBUG_MSG("\tAfter: " << ret << '\n');
    return ret;
  }

  virtual bool runOnModule(Module &M) {
    DEBUG_MSG_RED("Starting context insensitive PDG pass\n");

    // parse the database and print to stderr
    std::map<Value *, std::string> parseMap = ValToStrDB::parseIDMapFromModule(M);
    for (auto i = parseMap.begin(), e = parseMap.end(); i != e; ++i) {
      std::string id = rmLeadingZeros(rmBitvecConst(i->second));
      Value *v = i->first;
      errs() << '"' << id << '"' << " [label=\"" << *v << "\"];\n";
    }

    // IR was not modified
    return false;
  }

};

char ValDBToDot::ID = 0;
static RegisterPass<ValDBToDot> X("valdbtodot",
            "convert ValToStrDB to dot",
            false,  // unmodified CFG
            true); // analysis pass
