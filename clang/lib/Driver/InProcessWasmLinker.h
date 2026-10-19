//===- InProcessWasmLinker.h - In-process Wasm linker ---------------------===//

#ifndef LLVM_CLANG_DRIVER_INPROCESSWASMLINKER_H
#define LLVM_CLANG_DRIVER_INPROCESSWASMLINKER_H

#include "llvm/ADT/ArrayRef.h"

#include <string>

namespace clang {
namespace driver {

#if defined(__EMSCRIPTEN__)

int ExecuteInProcessWasmLinker(llvm::ArrayRef<const char *> Argv,
                               std::string *ErrMsg, bool *ExecutionFailed);

#endif

} // namespace driver
} // namespace clang

#endif // LLVM_CLANG_DRIVER_INPROCESSWASMLINKER_H