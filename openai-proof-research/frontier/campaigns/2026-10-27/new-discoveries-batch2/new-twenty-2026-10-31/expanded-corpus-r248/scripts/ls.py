"""List a directory (non-recursive, or recursive with -r up to 400 entries) with sizes (read-only)."""
import os, sys
args = sys.argv[1:]
rec = '-r' in args
args = [a for a in args if a != '-r']
for d in args:
    print('##', d)
    n = 0
    if rec:
        for dp, dns, fns in os.walk(d):
            for f in sorted(fns):
                p = os.path.join(dp, f)
                print(os.path.getsize(p), os.path.relpath(p, d))
                n += 1
                if n > 400:
                    break
            if n > 400:
                break
    else:
        for f in sorted(os.listdir(d)):
            p = os.path.join(d, f)
            print('d' if os.path.isdir(p) else os.path.getsize(p), f)
