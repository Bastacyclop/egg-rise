#!/bin/bash

NAMES=("lambda-compose-many"
"map-fission-fusion"
"base-to-scanline")

SUBSTITUTIONS=("explicit"
"extraction")

BINDINGS=("name"
"DeBruijn")

cargo build --release
mkdir -p results
rm results/*

for name in "${NAMES[@]}"
do
    for subs in "${SUBSTITUTIONS[@]}"
    do
        for bind in "${BINDINGS[@]}"
        do
            echo "benchmark: $name $subs $bind"
            name=$name subs=$subs bind=$bind systemd-run --user --scope -p MemoryLimit=2000M ./bench_aux.sh
        done
    done
done
