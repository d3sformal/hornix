add_executable(hornix main.cpp)

target_sources(hornix
        PRIVATE
        "CLI.cpp"
        "Preprocessing.cpp"
        "chc/Backend.cpp"
        "chc/ChcTransform.cpp"
        "chc/Helpers.cpp"
        "chc/SMTOut.cpp"
        "chc/utils/Liveness.cpp"
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

target_include_directories(hornix
  PRIVATE
        ${CMAKE_CURRENT_LIST_DIR}
)

# Optional: Enable RTTI if needed
if(LLVM_ENABLE_RTTI)
  target_compile_options(hornix PRIVATE -frtti)
endif()
