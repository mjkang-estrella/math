#!/usr/bin/env python3
"""Independent integer verification; no optimization package is used."""
import json
from pathlib import Path

WITNESSES = {
    6: [(0,0),(0,2),(0,3),(1,0),(1,3),(1,4),(2,0),(2,1),
        (3,1),(3,4),(4,2),(4,5),(5,0),(5,5)],
    9: [(0,0),(0,2),(1,2),(1,5),(2,0),(2,5),(2,8),(3,5),(3,6),
        (4,1),(4,3),(5,1),(5,3),(5,8),(6,4),(6,7),(7,6),(7,7),(8,3),(8,4)],
    12: [(0,3),(0,4),(0,8),(1,4),(1,7),(2,0),(2,6),(3,9),(3,10),
         (4,1),(4,2),(5,4),(5,5),(6,3),(6,7),(6,11),(7,0),(7,8),
         (8,3),(8,10),(9,2),(9,5),(10,6),(10,9),(11,1),(11,11)],
    15: [(0,5),(0,13),(1,2),(1,8),(2,8),(2,9),(2,14),(3,3),(3,5),
         (4,1),(4,12),(5,0),(5,10),(6,0),(6,12),(7,6),(7,7),(8,4),(8,11),
         (9,2),(9,13),(10,4),(10,9),(11,6),(11,14),(12,10),(12,11),
         (13,7),(13,14),(14,1),(14,3),(14,10)],
}

def check(k, entries):
    points = set(entries)
    assert len(points) == len(entries) == 2*k+2
    assert all(0 <= x < k and 0 <= y < k for x,y in points)
    labels = [lambda x,y:x, lambda x,y:y,
              lambda x,y:(x+y)%k, lambda x,y:(x-y)%k]
    counts = [[sum(f(x,y)==i for x,y in points) for i in range(k)] for f in labels]
    assert all(c >= 2 for row in counts for c in row)
    # Check actual parametric lines by a different enumeration.
    lines = {frozenset(((x+t*a)%k,(y+t*b)%k) for t in range(k))
             for x in range(k) for y in range(k)
             for a in [-1,0,1] for b in [-1,0,1] if (a,b)!=(0,0)}
    assert len(lines) == 4*k
    assert all(len(line & points) >= 2 for line in lines)
    return dict(k=k,card=len(points),points=entries,counts=counts,
                distinct_lines=len(lines),minimum_line_intersection=2)

if __name__ == '__main__':
    data = dict(status='exact witness verification PASS; no novelty claim',
                results=[check(k,p) for k,p in WITNESSES.items()])
    dest=Path(__file__).with_name('witness-check.json')
    dest.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))
