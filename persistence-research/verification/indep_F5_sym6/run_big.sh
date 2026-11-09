#!/bin/bash
cd /home/mj-kang/Documents/Dev/math/persistence-research/verification/indep5
for f in ../highdim/sym6/certs/pin6_180/K8_q6_c18_18_18_45_54_54_54.jsonl ../highdim/sym6/certs/pin6_180/K89_q6_c9_18_18_54_54_54_72.jsonl; do
  b=$(echo $f | sed 's|.*/certs/||; s|/|__|g'); o=../indep_F5_sym6/out/$b.json
  (ulimit -v 70000000; nice -n 5 timeout 18000 python3 -I check_sym_F5.py $f 11 --json > $o.tmp 2>&1 < /dev/null); mv $o.tmp $o &
done
wait; echo BIGDONE > ../indep_F5_sym6/BIGDONE
