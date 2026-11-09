#!/usr/bin/env python3
"""Read-only regex search in ONE file. Usage: grep.py FILE REGEX [CONTEXT_LINES] [MAXHITS]"""
import re, sys
p, rx = sys.argv[1], re.compile(sys.argv[2])
ctx = int(sys.argv[3]) if len(sys.argv) > 3 else 0
mx = int(sys.argv[4]) if len(sys.argv) > 4 else 50
lines = open(p, encoding='utf-8', errors='replace').read().split('\n')
n = 0
for i, l in enumerate(lines):
    if rx.search(l):
        n += 1
        if n > mx:
            print('... more hits'); break
        for j in range(max(0, i - ctx), min(len(lines), i + ctx + 1)):
            print(f'{j+1}:{lines[j][:400]}')
        if ctx:
            print('--')
