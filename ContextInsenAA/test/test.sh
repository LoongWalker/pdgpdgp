#!/bin/bash

set -e
set -u

die() {
  echo "${1:-}"
  exit 1
}

# test a single directory
if [ -z ${1:-} ]
then
  echo "Error: Pass test directory"
  exit 1
fi

echo "==== Testing: $1 ===="
cd $1 || exit 1
$RUN_IAA -datalog main.ll >out.bc || die "failed to run datalog pass"
diff main.ll.datalog datalog.expected || die "results failed to match expected"
echo "==== Test Passed ==== "
cd -
