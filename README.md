## README

Author: Markus Kusano

Collection of LLVM program analysis passes implemented using datalog.

The general flow of each analysis is:

1. Parse LLVM IR for facts about the program.
1. Combine facts with datalog program analysis specification.
1. Query datalog engine for results.

## Requirements

### LLVM

Note: this was built against LLVM 3.5. Newer versions of LLVM (e.g., 3.7) have
some API changes causing the build to fail. More information on linking to
non-system installations of LLVM can be seen below (Build Options).

### Z3

Requires the Z3 library files to be built. Again, if these are in non-standard
locations, see below. The syntax used in `.smt2` files has changed a bit,
particularly for making queries. This was tested using Z3 commit
cee7dd39444c9060186df79c2a2c7f8845de415b


## Building
The passes are built using `cmake`. They require LLVM (tested on 3.5).

To build, first create a directory for the build files.

    mkdir build
    cd build

Then, run `cmake` passing the uppermost directory of this repo

    cmake ../

Then, simply run `make`

    make

The result will be a set of `.so` files that can be loaded with `opt`'s `-load`
command.

### Build Options

By default, `cmake` will search for the LLVM `cmake` file in some standard
locations. If you would like to specify the location, use the variable
`LLVM_DIR`. It should be set to the directory containing the `LLVMConfig.cmake`
file. It is located at `<LLVM Install Directory>/share/llvm/cmake`. For
example, run the following in the build directory:

    cmake -DLLVM_DIR=/home/markus/src/install-3.5/share/llvm/cmake ../

## Z3

The datalog engine used in Z3 is required. Follow their build instructions:

    https://z3.codeplex.com/

If Z3 is installed in a non-standard location the CMake variables `Z3_LIB` and
`Z3_INC` should be set to the lib and include directories of the install. Use
`-DZ3_LIB=...` and `-DZ3_INC=...`

## Directory Layout

`./utils` contains some common code shared amongst passes.

### ContextInsenAA
`./ContextInsenAA` contains a context insensitive alias analysis. It supports
tracing not only back to malloc but also across all pointer arithmetic. It
supports loads and stores of pointers. For example:
  
    store i8** %argv, i8*** %2, align 8
    %3 = load i8*** %2, align 8

In this example, there is an assignment of `argv` to a single indirection `%2`
(of type `i8**`). The subsequent `load` of `%3` does not alias `%2` but rather
aliases `*%2` which is `argv`.

### ContextInsenPDG

A interprocedural context-insensitive calculation of the program dependence
graph. This is the combination of the control and data dependence graph.
Includes dependency edges caused by aliasing.

The underlying alias analysis is the same as ContextInsenAA (context
insensitive, interprocedural)

### ContextInsenDynPDG

Same as ContextInsenPDG but supports dynamic dispatch (i.e., function
pointers). The point-to relation for functions is mutually calculated along
with the inter-procedural dependency relation.

### ValDBToDot

Given a LLVM bit-code file filled with a Value database (see
`utils/ValToStrDb.{cpp,h}`) this will output the name of each node to DOT
format. This can be used after an analysis is run and you want to examine the
graphical results.
