//===-- UniSan.cc - the UniSan framework------------------------===//
//
// This file implemets the UniSan framework. It calls the pass for
// building call-graph and the pass for finding unsafe allocations.
// It outputs the information of unsafe allocations for further
// instrumentation (i.e., zero-initialization). The iterative
// analysis strategy is borrowed from KINT[OSDI'12] to avoid
// combining all bitcode files into a single one.
//
//===-----------------------------------------------------------===//

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Verifier.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/Bitcode/BitcodeWriter.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/ToolOutputFile.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/IRReader/IRReader.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/Path.h"

#include <memory>
#include <vector>
#include <sstream>
#include <sys/resource.h>

#include "Kmeld.h"
#include "CriticalFunc.h"

using namespace llvm;

// Command line parameters.
cl::opt<unsigned> VerboseLevel(
    "verbose-level", cl::desc("Print information at which verbose level"),
    cl::init(0));

cl::opt<bool> FoiCollection(
    "foi-collection",
    cl::desc("Collect initial set of FOIs"),
    cl::NotHidden, cl::init(false));

cl::opt<bool> CallGraph(
    "call-graph",
    cl::desc("Construct global Call Graph"),
    cl::NotHidden, cl::init(false));

cl::opt<bool> Ownership(
    "ownership-analysis",
    cl::desc("Perform Ownership reasoning Pass (Escape analysis & Consumer detection)"),
    cl::NotHidden, cl::init(false));

int main(int argc, char **argv)
{
  sys::PrintStackTraceOnErrorSignal(argv[0]);
  PrettyStackTraceProgram X(argc, argv);

  // llvm_shutdown_obj Y;  // Call llvm_shutdown() on exit.

  cl::ParseCommandLineOptions(argc, argv, "global analysis\n");

  // Main workflow

  // Build global callgraph.
  if (CallGraph)
  {
    CallGraphMain();
  }
  if (FoiCollection)
  {
    FOIcollect();
  }

  if (Ownership)
  {
    SequenceMine();
  }

  return 0;
}
