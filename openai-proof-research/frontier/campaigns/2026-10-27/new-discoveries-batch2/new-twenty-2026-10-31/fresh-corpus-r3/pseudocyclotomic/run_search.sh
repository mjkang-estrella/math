#!/bin/bash
# bounded single-process searches (<=1 CPU each, two at a time max)
export OMP_NUM_THREADS=1
python3 pseudo.py 15 60 odd > search_odd_p15_q60.log 2>&1 &
python3 -c "
import pseudo,sys
" 
wait
