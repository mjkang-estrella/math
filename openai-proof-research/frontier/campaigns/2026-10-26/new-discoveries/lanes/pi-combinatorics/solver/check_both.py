#!/usr/bin/env python3
"""Check all verified violation boards under both rule variants."""
import json, glob, sys
import brute, verify, gen2

rows = []
for fn in sorted(glob.glob('violation_*.json')):
    bd = json.load(open(fn))
    try:
        verify.verify(bd)
    except AssertionError as ex:
        continue
    text = gen2.to_text(bd)
    open('/tmp/b.txt', 'w').write(text)
    n, edges, faces = brute.read_board('/tmp/b.txt')
    wf = brute.solve(n, edges, faces, chordless=False)
    wc = brute.solve(n, edges, faces, chordless=True)
    m = len(edges)
    pred = 'P1' if m % 2 == 1 else 'P2'
    rows.append((fn, m, pred, wf, wc))
    print(f"{fn}: m={m} parity-predicts={pred} face-rule={wf} chordless-rule={wc}")

print()
print("Violation under BOTH rules:")
for fn, m, pred, wf, wc in rows:
    if wf != pred and wc != pred:
        print(f"  {fn} m={m} predicts={pred} face={wf} chordless={wc}")
