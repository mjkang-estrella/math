# Reducibility test for the deepest-triangle contraction in cubic Halin graphs (2-tone 6-colourings).
# H: deepest internal x with leaf children x1, xl (triangle), parent y; cycle ... x_{l-1} xl x1 x2 ...
# H' = H with the triangle contracted to a leaf z adjacent to y, x2, x_{l-1}.
# Given a 2-tone 6-colouring phi of H', keep phi off {x,x1,xl}; we need labels Px,P1,Pl.
# Boundary data (generic, only constraints implied by validity of phi on H'):
#   Z=phi(z); Y,A,B = phi(y),phi(x2),phi(x_{l-1}); Fx = labels of y's other nbrs;
#   F1 = labels of x2's other nbrs (x3, y2); Fl = labels of x_{l-1}'s other nbrs.
# New constraints in H: Px,P1,Pl pairwise disjoint; Px&Y=0, P1&A=0, Pl&B=0;
#   Px not in Fx u {A,B}; P1 not in F1 u {Y,B}; Pl not in Fl u {Y,A}.
# usage: halinreduce.py
import itertools
C = list(range(6))
LAB = [frozenset(p) for p in itertools.combinations(C, 2)]
def disj(a, b): return not (a & b)
Z = frozenset({0, 1})
W = [l for l in LAB if disj(l, Z)]
assign = [(px, p1, pl) for px in LAB for p1 in LAB for pl in LAB if disj(px, p1) and disj(px, pl) and disj(p1, pl)]
def pairsets(base, excl):
    cand = [l for l in LAB if disj(l, base) and l != Z and l not in excl]
    return [frozenset(s) for s in itertools.combinations(cand, 2)]
fails = []; total = 0
for Y, A, B in itertools.permutations(W, 3):
    FX = pairsets(Y, ()); F1 = pairsets(A, ()); FL = pairsets(B, ())
    for fx in FX:
        for f1 in F1:
            for fl in FL:
                total += 1
                ok = False
                for px, p1, pl in assign:
                    if not disj(px, Y) or not disj(p1, A) or not disj(pl, B): continue
                    if px in fx or px == A or px == B: continue
                    if p1 in f1 or p1 == Y or p1 == B: continue
                    if pl in fl or pl == Y or pl == A: continue
                    ok = True; break
                if not ok: fails.append((Y, A, B, fx, f1, fl))
print('boundary cases', total, 'non-extendable', len(fails))
for f in fails[:5]: print(' ', [sorted(map(sorted, x)) if isinstance(x, frozenset) and all(isinstance(e, frozenset) for e in x) else sorted(x) for x in f])
