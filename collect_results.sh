#!/bin/bash

echo goal, subs, bind, found, seconds, time, kbytes, rules, e-graph
for file in results/*
do
    f=$(basename $file)
    goal=$(echo $f | cut -d _ -f1)
    subs=$(echo $f | cut -d _ -f2)
    bind=$(echo $f | cut -d _ -f3)
    stop=$(grep -oP ".*Stop reason:\K.*" $file | sed 's/^ //g' | sed 's/ $//g')
    seconds=$(grep -oP ".*Total time:\K.*" $file | sed 's/^ //g' | sed 's/ $//g')
    egraph=$(grep -oP ".*Egraph size:\K.*" $file | sed 's/^ //g' | sed 's/ $//g')
    rules=$(grep -oP ".*applied rules:\K.*" $file | sed 's/^ //g' | sed 's/ $//g')
    found="no"
    if [ "$stop" = "Other(\"Done\")" ]; then
        found="yes"
    fi
    time=$(grep -oP ".*(?= \[h:\]m:s)" $file)
    kbytes=$(grep -oP "[0-9]*(?= Kbytes)" $file)
    echo $goal, $subs, $bind, $found, $seconds, $time, $kbytes, $rules, "'$egraph'"
done