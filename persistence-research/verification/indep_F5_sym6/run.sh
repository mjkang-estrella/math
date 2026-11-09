#!/bin/bash
# Parent: replay every sym6 deep-pin certificate with F5's independent checker (resumable).
# Pass 1: 6 GB cap, 16 workers. Pass 2: anything not PASS retried at 30 GB, 2 workers.
cd /home/mj-kang/Documents/Dev/math/persistence-research/verification/indep5
L=../indep_F5_sym6
run1() { f=$1; b=$(echo $f | sed 's|.*/certs/||; s|/|__|g'); o=$L/out/$b.json; [ -s $o ] && grep -q '"result": "PASS"' $o && return 0
  (ulimit -v 6000000; nice -n 10 timeout 3600 python3 -I check_sym_F5.py $f 11 --json > $o.tmp 2>/dev/null < /dev/null); mv $o.tmp $o; }
run2() { f=$1; b=$(echo $f | sed 's|.*/certs/||; s|/|__|g'); o=$L/out/$b.json; grep -q '"result": "PASS"' $o 2>/dev/null && return 0
  (ulimit -v 30000000; nice -n 10 timeout 7200 python3 -I check_sym_F5.py $f 11 --json > $o.tmp 2>/dev/null < /dev/null); mv $o.tmp $o; }
export -f run1 run2; export L
cat ../highdim/sym6/deep_pin_certs.txt | xargs -P 16 -I{} bash -c 'run1 {}'
cat ../highdim/sym6/deep_pin_certs.txt | xargs -P 2 -I{} bash -c 'run2 {}'
echo DONE > $L/DONE
