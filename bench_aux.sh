#!/bin/sh

RESULTS="results/${name}_${subs}_${bind}"

echo "search_name, iteration_number, physical_memory, virtual_memory, e-nodes, e-classes, terms_uts, applied_rules, total_time, hook_time, search_time, apply_time, rebuild_time, found" > ${RESULTS}

(command time -f "%E [h:]m:s, %M Kbytes" timeout -v 5m ./target/release/egg-rise "${name}" "${subs}" "${bind}") 2>> ${RESULTS}