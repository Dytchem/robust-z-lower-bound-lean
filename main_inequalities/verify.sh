#!/bin/sh
# Check every file of this folder: each is elaborated in the Lean tree that holds its proof core,
# against that tree's prebuilt Mathlib, and prints the axioms of its theorems.
set -e
HERE=$(cd "$(dirname "$0")" && pwd)
PATH="$HOME/.elan/bin:$PATH"
export PATH

check() {
  echo "check $2  [$1]"
  ( cd "$HERE/../lean_sharp/$1" && lake env lean "$HERE/$2" )
}

check wC Elementary.lean
check wF Jensen.lean
check wM WeakConstant.lean
check wC ExactCriterion.lean
check wC Certificates.lean
check wC LinearGrowth.lean
