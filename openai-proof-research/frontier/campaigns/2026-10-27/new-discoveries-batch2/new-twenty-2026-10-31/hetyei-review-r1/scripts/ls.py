#!/usr/bin/env python3
"""Read-only: list entries of one directory (non-recursive), or with a name filter.
Usage: ls.py DIR [SUBSTRING]"""
import os, sys
d = sys.argv[1]
sub = sys.argv[2] if len(sys.argv) > 2 else ''
for e in sorted(os.listdir(d)):
    if sub in e:
        p = os.path.join(d, e)
        print(('D ' if os.path.isdir(p) else 'F ') + e)
