import pathlib, re, sys
# Usage: ctx.py LANE_DIR TEXTSTEM REGEX [MAXHITS] [BEFORE] [AFTER]
D = pathlib.Path(sys.argv[1]).resolve()
s = (D / 'sources' / 'text' / (sys.argv[2] + '.txt')).read_text()
n = int(sys.argv[4]) if len(sys.argv) > 4 else 6
b = int(sys.argv[5]) if len(sys.argv) > 5 else 300
a = int(sys.argv[6]) if len(sys.argv) > 6 else 1500
for m in list(re.finditer(sys.argv[3], s, re.I))[:n]:
    print('---- @', m.start()); print(s[max(0, m.start() - b):m.end() + a]); print()
