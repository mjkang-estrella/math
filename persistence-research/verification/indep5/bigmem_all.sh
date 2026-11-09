#!/bin/bash
tail -n +2 bad_paths.txt | while read -r p; do
  echo "=== $p" >> bigmem_results.txt
  ( ulimit -v 30000000; python3 -I ./check_sym_F5.py "$p" 11 --json ) >> bigmem_results.txt 2>&1
done
echo DONE >> bigmem_results.txt
