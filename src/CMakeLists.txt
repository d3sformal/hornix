add_executable(hornix main.cpp)

target_sources(hornix
        PRIVATE
        "CLI.cpp"
        "Preprocessing.cpp"
        "chc/ChcTransform.cpp"
        "chc/SMTOut.cpp"
        "chc/Backend.cpp"
)

include_directories(${LLVM_INCLUDE_DIRS})
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

# Link against namespaced LLVM targets (modern way)
target_link_libraries(hornix
  PRIVATE
    LLVMCore
    LLVMSupport
    LLVMIRReader
    LLVMPasses
    LLVMScalarOpts
)

# Optional: Enable RTTI if needed
if(LLVM_ENABLE_RTTI)
  target_compile_options(hornix PRIVATE -frtti)
endif()
