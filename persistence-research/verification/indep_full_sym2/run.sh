#!/bin/bash
# Parent: full replay of every sym2 certificate with Agent F's independent checker (resumable).
cd /home/mj-kang/Documents/Dev/math/persistence-research/verification/indep4
cat ../indep_full_sym2/all_certs.txt | xargs -P 8 -I{} bash -c 'f={}; b=$(basename $(dirname $f))__$(basename $f); o=../indep_full_sym2/out/$b.json; [ -s $o ] && exit 0; ulimit -v 6000000; nice -n 19 timeout 3600 python3 -I check_sym_F.py $f 11 --json > $o.tmp 2>/dev/null < /dev/null; mv $o.tmp $o'
echo DONE > ../indep_full_sym2/DONE
