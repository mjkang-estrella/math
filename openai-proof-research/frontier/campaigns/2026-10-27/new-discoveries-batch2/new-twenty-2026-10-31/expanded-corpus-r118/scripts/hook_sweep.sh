#!/bin/bash
# sweep N for given r until first hook collision or N max
cd "$(dirname "$0")/.."; r=$1; for N in $(seq $2 $3); do o=$(scripts/hookcoll $r $N); echo "$o" | tail -1; if ! echo "$o" | tail -1 | grep -q 'collisions(adjacent)=0'; then echo "$o" | head -2; break; fi; done
