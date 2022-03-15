#!/bin/sh

(command time -f "%E [h:]m:s, %M Kbytes" timeout -v 5m ./target/release/egg-rise "${name}" "${subs}" "${bind}") &> "results/${name}_${subs}_${bind}"