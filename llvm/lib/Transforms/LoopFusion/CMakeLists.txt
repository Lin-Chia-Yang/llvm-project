add_llvm_component_library(LLVMTransformLoopFusion
  CodeMotion.cpp
  IndexUnification.cpp
  PeelLoop.cpp

  ADDITIONAL_HEADER_DIRS
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms
  ${LLVM_MAIN_INCLUDE_DIR}/llvm/Transforms/LoopFusion

  DEPENDS
  intrinsics_gen

  LINK_COMPONENTS
  Analysis
  Core
  Support
  TargetParser
  )
