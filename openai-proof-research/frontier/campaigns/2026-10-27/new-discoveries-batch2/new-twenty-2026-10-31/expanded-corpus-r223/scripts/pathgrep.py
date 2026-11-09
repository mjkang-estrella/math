import sys, json, pathlib
# usage: pathgrep.py FILE term [term...]: print lines (<=300 chars) containing any term (case-insensitive)
t = pathlib.Path(sys.argv[1]).read_text(errors='replace').splitlines()
terms = [x.lower() for x in sys.argv[2:]]
for i, line in enumerate(t, 1):
    l = line.lower()
    if any(x in l for x in terms):
        print(i, line[:300])
