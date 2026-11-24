#!/usr/bin/env python3
"""Small editor for public-claim-100/LANES.json.
  lane KEY TASK MODEL FOLDER [id,id]   add a lane (prefix 5)
  done KEY TEXT                        mark a lane done with a note
  cand ID TEXT                         append TEXT to the candidate entry (creates it)
  note TEXT                            append a note
"""
import json, sys, os, time
p = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), 'LANES.json')
d = json.load(open(p)); a = sys.argv[1:]
if a[0] == 'lane':
    e = {'task': a[2], 'model': a[3], 'prefix': 5, 'folder': a[4]}
    if len(a) > 5: e['ids'] = [int(x) for x in a[5].split(',')]
    d['lanes'][a[1]] = e
elif a[0] == 'done': d['lanes'][a[1]]['done'] = a[2]
elif a[0] == 'cand': d['candidates'][a[1]] = (d['candidates'].get(a[1], '') + ' ' + a[2]).strip()
elif a[0] == 'note': d['notes'].append(time.strftime('%H:%M PST %m-%d: ') + a[1])
json.dump(d, open(p, 'w'), indent=1)
