#!/bin/bash
# retry wrapper for the flaky runner thread-creation (-6); usage: retry.sh <label> <args...>
cd "$(dirname "$0")"; source env.sh
for i in 1 2 3 4 5 6 7 8; do
  python3 -I -B runner.py "$@" 2>&1|tail -1|grep -o 'EXIT=[0-9-]*'
  E=$(grep -o 'EXIT [-0-9]*' "logs/$(ls -t logs|head -1)"|head -1|awk '{print $2}')
  case "$E" in 0|1) exit $E;; esac
  sleep $((15+i*5))
done
exit 9
