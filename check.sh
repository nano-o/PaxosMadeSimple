#!/bin/bash

set -e
set -x

case "$1" in
    -typecheck)
        shift
        FILE="Apa${1}.tla"
        $APA/bin/apalache-mc typecheck $FILE
        ;;
    -inductive)
        shift
        FILE="Apa${2}.tla"
        $APA/bin/apalache-mc check --init=Init --inv=$1 --length=0 $FILE
        JVM_ARGS="-Xmx25G" time $APA/bin/apalache-mc check --tuning-options=search.invariant.mode=after:"search.invariantFilter=1->.*" --init="${1}_" --inv=$1 --length=1 $FILE
        ;;
    -inductive-step-only)
        shift
        FILE="Apa${2}.tla"
        time $APA/bin/apalache-mc check --tuning-options=search.invariant.mode=after:"search.invariantFilter=1->.*" --init="${1}_" --inv=$1 --length=1 $FILE
        ;;
    -implication)
        shift
        FILE="Apa${2}.tla"
        $APA/bin/apalache-mc check --tuning-options=search.invariant.mode=after --init="${1}_ante" --inv=$1 --length=0 $FILE
        ;;
esac
