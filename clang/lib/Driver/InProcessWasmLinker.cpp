//===- InProcessWasmLinker.cpp - In-process Wasm linker -------------------===//

#include "InProcessWasmLinker.h"

#if defined(__EMSCRIPTEN__) && defined(CLANG_ENABLE_IN_PROCESS_WASM_LINKER)

#include "lld/Common/Driver.h"
#include "llvm/Support/raw_ostream.h"

LLD_HAS_DRIVER(wasm)

namespace clang {
namespace driver {

int ExecuteInProcessWasmLinker(llvm::ArrayRef<const char *> Argv,
                               std::string *ErrMsg, bool *ExecutionFailed) {
  const lld::DriverDef WasmDriver = {lld::Flavor::Wasm, &lld::wasm::link};
  const lld::Result Result =
      lld::lldMain(Argv, llvm::outs(), llvm::errs(), {WasmDriver});

  if (ExecutionFailed)
    *ExecutionFailed = false;

  return Result.retCode;
}

} // namespace driver
} // namespace clang

#endif