# Sets up some shell variables to easy access to LLVM passes

#### Edit these variables accordingly
# Location where LLVM is installed
export LLVM_INSTALL_DIR=/usr/bin

# Location of datalog library files
export PASSES=`pwd`/../../build
######

#### The following variables should not have to be modified
# Location of Context Insensitive Alias Analysis SO file
export CONTEXT_INSEN_SO=${PASSES}/ContextInsenAA/libDatalogCIAA.so
# Name of context insensitive pass
export CONTEXT_INSEN="contextinsen-aa"

export OPT=${LLVM_INSTALL_DIR}/opt
export CLANG=${LLVM_INSTALL_DIR}/clang
export CLANG='${LLVM_INSTALL_DIR}/clang++'

# OPT command to run context insensitive AA. Just pass input BC file and
# redirect the output
export RUN_IAA="$OPT -load $CONTEXT_INSEN_SO -$CONTEXT_INSEN"
