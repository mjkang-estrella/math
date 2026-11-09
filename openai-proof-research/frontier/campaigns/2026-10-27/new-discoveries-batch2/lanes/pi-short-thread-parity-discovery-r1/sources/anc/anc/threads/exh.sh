#!/bin/bash
# exh.sh L n : exhaustive check of all twin-free pieces with threads<=L on n vertices (certificate solver)
L=$1; n=$2
start=$(date +%s)
res=$(./genpieces $L $n 2>/dev/null | nice ./parsolve2 -limit 6 2>/tmp/claude-ps-$L-$n.err | awk '{c[$3]++; tot++; if (($1%2)!=($2%2)||$1>1) {b++; print "VIOLATION", $0 > "/dev/stderr"}} END {printf "pieces=%d par=%d exact=%d violations=%d", tot, c["par"]+0, c["exact"]+0, b+0}')
echo "L=$L n=$n E=$((n-1)) $res time=$(( $(date +%s) - start ))s $(cat /tmp/claude-ps-$L-$n.err | tr '\n' ' ')"
