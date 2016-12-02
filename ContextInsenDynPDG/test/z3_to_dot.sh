#!/bin/bash
# Given the output of a two variable relation from Z3, convert it to DOT

set -e
set -u

die() {
  echo ${1:-}
  exit 1
}

if [ -z ${1:-} ]
then
  die "Pass as first argument output of Z3"
fi

# remove the first line
sed 1d $1 | \
# remove the "(or "
sed 's/^(or //g' | \
# remove leading whitespace
sed 's/^[ \t]*//' | \
# remove the and condition from the begining of each line
sed 's/(and (= (:var 0) //g' | \
# convert the string between the two variables names to an arrow
sed 's/(= (:var 1)/->/g' | \
# remove all parentheses at the end of the line
sed 's/)//g' | \
# remove leading zeros in expressions
sed 's/#x0*//g' | \
# put quotes around variables
sed 's/[a-zA-Z0-9]\+/"&"/g'
