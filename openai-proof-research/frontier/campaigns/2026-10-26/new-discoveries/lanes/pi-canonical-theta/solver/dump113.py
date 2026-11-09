#!/usr/bin/env python3
"""Dump the winner's winning-response sets after each opponent move,
organized by state pattern, to reverse-engineer a uniform strategy."""
import sys
from analyze113 import Board

def pattern(b, state):
    """Human-readable pattern: for each path, the run structure."""
    names = b.edge_names()
    tri = b.digits(state)
    s = {}
    for pi, L in enumerate(b.paths):
        st = b.starts[pi]
        s[f"P{pi}"] = ''.join('.F.B'[tri[st+i]] for i in range(L))
    s['a'] = '.F.B'[tri[0]]  # P0[0] is the single A edge
    return s

def main():
    k = int(sys.argv[1]); outer = int(sys.argv[2])
    mode = sys.argv[3] if len(sys.argv) > 3 else 'responses'
    b = Board(1, 3, k, outer)
    w = b.solve(0)
    m = b.m
    names = b.edge_names()
    print(f"Theta(1,3,{k}) outer={outer} m={m} winner P{w} states={len(b.memo)}")
    if mode == 'responses':
        # for each reachable state with loser to move: loser plays (e,d) -> winner's winning replies
        seen = b.reachable()
        shown = 0
        for st in sorted(seen):
            if b.player(st) != 3 - w:
                continue
            tri = b.digits(st)
            for e in range(m):
                if tri[e]: continue
                for d in (1, 2):
                    eff = b.move_effects(st, e, d)
                    if eff is None: continue
                    if eff == 'win':
                        print(f"  LOSER WINS BY CELL: {b.state_str(st)} loser plays {names[e]} {'F' if d==1 else 'B'}")
                        continue
                    ns = st + d * b.pw3[e]
                    wm = []
                    for e2 in range(m):
                        if (ns // b.pw3[e2]) % 3: continue
                        for d2 in (1, 2):
                            eff2 = b.move_effects(ns, e2, d2)
                            if eff2 == 'win':
                                wm.append((names[e2], 'F' if d2==1 else 'B', 'WIN'))
                            elif eff2 == 'ok' and b.solve(ns + d2*b.pw3[e2]) == w:
                                wm.append((names[e2], 'F' if d2==1 else 'B', ''))
                    if not wm:
                        print(f"  !! loser move {names[e]} {'F' if d==1 else 'B'} from {b.state_str(st)} leaves NO winning reply")
                    shown += 1
        print(f"  ({shown} loser moves checked)")

if __name__ == '__main__':
    main()
