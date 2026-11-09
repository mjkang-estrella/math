#!/bin/bash
# Sweep all 1<=k<=n-2 for given n with the conjecture's cap h<=k.
n=$1; for ((k=1;k<=n-2;k++)); do bin/zerosum $n $k; done
