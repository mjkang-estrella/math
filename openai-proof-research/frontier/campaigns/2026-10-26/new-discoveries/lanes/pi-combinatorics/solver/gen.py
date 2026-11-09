#!/usr/bin/env python3
"""Generators for Game of Cycles boards + validation suite.

Graph text format (for solve.js):
  n m / m lines "u v" / f / f lines: "k v0 ... v_{k-1}" (bounded face, cyclic)
"""
import subprocess, sys, os

SOLVER = os.path.join(os.path.dirname(__file__), 'solve.js')

def solve(text, verbose=False):
    r = subprocess.run(['node', SOLVER] + (['-v'] if verbose else []),
                       input=text, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(r.stderr)
    if verbose:
        print(r.stderr.strip(), file=sys.stderr)
    return r.stdout.strip()

def cycle_board(n):
    """C_n with its single bounded cell."""
    lines = [f"{n} {n}"]
    for i in range(n): lines.append(f"{i} {(i+1)%n}")
    lines.append("1")
    lines.append(" ".join(str(i) for i in range(n)))
    return "\n".join(lines) + "\n"

def k4_board():
    edges = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
    faces = [(0,3,1),(1,3,2),(2,0,3)]  # 3 inside triangle 012
    return board_text(4, edges, faces)

def cycle_chord_board(n, chord=None):
    """C_n plus one chord (0,k); faces (0..k) and (0,k..n-1)."""
    k = chord[0] if chord else n//2
    edges = [(i,(i+1)%n) for i in range(n)] + [(0,k)]
    f1 = list(range(0,k+1)); f2 = [0]+list(range(k,n))
    return board_text(n, edges, [f1,f2])

def theta_board(j,k,l, outer=None, chordless=False):
    """Theta graph: three paths between u=0 and v=1 of lengths j,k,l.
    outer = index of the path-pair that is the outer face (0..2 meaning
    pair (0,1),(1,2),(0,2)). Default: pair (0,2) i.e. paths j and l outer.
    chordless=True: list all three pair-cycles as winning cycles."""
    paths = [j,k,l]
    edges = []; nxt = 2
    internals = []
    for L in paths:
        chain = [0] + list(range(nxt, nxt+L-1)) + [1]
        nxt += L-1
        internals.append(chain)
        for a,b in zip(chain, chain[1:]): edges.append((a,b))
    pairs = [(0,1),(1,2),(0,2)]
    faces = []
    for (a,b) in pairs:
        if outer is not None and (a,b) == [(0,1),(1,2),(0,2)][outer]: continue
        if not chordless and outer is None and (a,b) == (0,2): continue
        seq = internals[a][:-1][::-1] + internals[b]  # a-path reversed into 1, then b-path back to 0? 
        # cyclic: 0 -> (path a) -> 1 -> (path b reversed) -> 0
        seq = internals[a] + internals[b][-2:0:-1]
        faces.append(seq)
    return board_text(nxt-1+1, edges, faces)

def board_text(n, edges, faces):
    lines = [f"{n} {len(edges)}"]
    lines += [f"{u} {v}" for u,v in edges]
    lines.append(str(len(faces)))
    for seq in faces:
        lines.append(str(len(seq)) + " " + " ".join(map(str,seq)))
    return "\n".join(lines) + "\n"

def fig16_board():
    """BBFS Fig 16: triangle b,c,d + pendant a-b. Vertices: a=3,b=0,c=1,d=2."""
    edges = [(0,1),(1,2),(2,0),(0,3)]
    faces = [(0,1,2)]
    return board_text(4, edges, faces)

if __name__ == '__main__':
    fails = 0
    def check(name, text, expect):
        global fails
        got = solve(text)
        ok = got == expect
        print(f"{'OK ' if ok else 'FAIL'} {name}: got {got}, expected {expect}")
        if not ok: fails += 1

    # Theorem 3 (AMM): C_n parity
    for n in range(3, 9):
        check(f"C_{n}", cycle_board(n), "P1" if n % 2 == 1 else "P2")
    # Theorem 1: K4 -> P2
    check("K4", k4_board(), "P2")
    # Theorem 4: C_n + chord: n even -> P1, n odd -> P2
    for n in (4,5,6,7):
        check(f"C_{n}+chord", cycle_chord_board(n), "P1" if n % 2 == 0 else "P2")
    # Fig 16 counterexample: P1 on 4 edges (degree-1 vertex present)
    check("Fig16 (4 edges, pendant)", fig16_board(), "P1")
    # BBFS sample game Theta(2,2,2), 6 edges: P2 wins
    check("Theta(2,2,2)", theta_board(2,2,2), "P2")
    # Corollary 7.1: Theta(j,2,k): j+k odd -> P1, even -> P2
    check("Theta(1,2,2) [j+k=3 odd]", theta_board(1,2,2), "P1")
    check("Theta(3,2,5) [j+k=8 even]", theta_board(3,2,5), "P2")
    print("done", file=sys.stderr)
    sys.exit(1 if fails else 0)
