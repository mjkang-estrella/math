"""Print context windows around a regex in a text file (read-only).
usage: ctx.py FILE REGEX [BEFORE] [AFTER] [MAXHITS]"""
import re
import sys

path, pat = sys.argv[1], sys.argv[2]
before = int(sys.argv[3]) if len(sys.argv) > 3 else 300
after = int(sys.argv[4]) if len(sys.argv) > 4 else 1500
maxhits = int(sys.argv[5]) if len(sys.argv) > 5 else 6
t = open(path, encoding='utf-8', errors='replace').read()
n = 0
for m in re.finditer(pat, t):
    n += 1
    if n > maxhits:
        break
    print(f'@@ offset {m.start()}')
    print(t[max(0, m.start() - before):m.start() + after])
    print('-' * 40)
print('total hits shown', min(n, maxhits))
