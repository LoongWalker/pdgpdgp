#!/bin/bash

set -e
#set -u

TEST_DIRS="argv01 \
  call01 \
  malloc01"

die () {
  echo "$0:" "$@" >&2
  exit 1
}

for d in $TEST_DIRS
do
  ./test.sh $d || die "Test failed"
done
