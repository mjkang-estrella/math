#!/bin/bash
# exh_save.sh L n : like exh.sh but saves pieces and results, and lists violating pieces
L=$1; n=$2
start=$(date +%s)
./genpieces $L $n 2>/dev/null > data/pieces_L${L}_n${n}.txt
nice ./parsolve2 -limit 6 < data/pieces_L${L}_n${n}.txt 2>/tmp/claude-ps-$L-$n.err > data/res_L${L}_n${n}.txt
paste -d' ' data/res_L${L}_n${n}.txt data/pieces_L${L}_n${n}.txt | awk '($1%2)!=($2%2)||$1>1' > data/viol_L${L}_n${n}.txt
echo "L=$L n=$n E=$((n-1)) pieces=$(wc -l < data/pieces_L${L}_n${n}.txt) violations=$(wc -l < data/viol_L${L}_n${n}.txt) methods: $(awk '{print $3}' data/res_L${L}_n${n}.txt | sort | uniq -c | tr '\n' ' ') time=$(( $(date +%s) - start ))s $(cat /tmp/claude-ps-$L-$n.err | tr '\n' ' ')"
