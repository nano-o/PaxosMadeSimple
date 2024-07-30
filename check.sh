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
        $APA/bin/apalache-mc check --init=Init --inv=$1 --length=0 --config="Apa${2}.cfg" $FILE
        JVM_ARGS="-Xmx25G" time $APA/bin/apalache-mc check --tuning-options=search.invariant.mode=after:"search.invariantFilter=1->.*" --init="${1}_" --inv=${1} --length=1 --config="Apa${2}.cfg" $FILE
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
    -tlc)
        shift
        java -Xmx50G -Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet -Dtlc2.tool.ModelChecker.BAQueue=true -cp tla2tools.jar -XX:+UseParallelGC tlc2.TLC "${1}.tla" -workers 20 -deadlock
        ;;
esac
