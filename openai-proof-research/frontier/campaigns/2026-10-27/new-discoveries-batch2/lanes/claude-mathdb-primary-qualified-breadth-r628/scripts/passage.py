# Print source-text windows for given regex labels from a bound text snapshot (read-only).
import re, sys
t = open(sys.argv[1], encoding='utf-8', errors='replace').read()
n = int(sys.argv[2])
for lab in sys.argv[3:]:
    hits = [m.start() for m in re.finditer(lab, t)]
    print('#### %s hits=%s' % (lab, hits[:12]))
    for h in hits[:3]:
        print('@%d: %s' % (h, t[h:h + n].replace('\n', ' ')))
