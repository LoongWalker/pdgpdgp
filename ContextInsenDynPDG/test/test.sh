#!/bin/bash

set -e
set -u

die() {
  if [ ! -z "${1:-}" ]
  then
    echo "$1"
  fi
  exit 1
}

# test a single directory
if [ -z "${1:-}" ]
then
  echo "Error: Pass test directory"
  exit 1
fi

echo "==== Testing: $1 ===="
cd $1 || exit 1
$RUN_PDG main.ll >out.bc || die "failed to run datalog pass"
diff main.ll.smt2 smt2.expected || die "results failed to match expected"
echo "==== Test Passed ==== "
cd -
