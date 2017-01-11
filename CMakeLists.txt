cmake_minimum_required(VERSION 2.8.8)
project(LLVMDatalog)

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")


find_path(Z3_INC z3++.h)
message(STATUS ${Z3_INC})

# Set your project compile flags. E.g. if using the C++ header files you will
# need to enable C++11 support for your compiler.

add_definitions(${LLVM_DEFINITIONS} -std=c++11 -Wall -g -fno-rtti)
include_directories(${LLVM_INCLUDE_DIRS} ${Z3_INC})

#add_subdirectory(ContextInsenAA)
#add_subdirectory(ContextInsenPDG)
add_subdirectory(ContextInsenDynPDG)
add_subdirectory(ValDBToDot)
#add_subdirectory(DynSliceSelect)
