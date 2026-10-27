#!/usr/bin/env python3
"""Search for non-convergent orbits of IGN N(x)=x/(Bx), B=I+A, connected simple graphs.

Scale-invariant map: T(cx)=T(x). All orbits live in (0,1]^n after one step.
Detect: (a) non-convergence of the projective direction, (b) period-k cycles,
(c) slow drift. Report worst cases.
"""
import numpy as np
import itertools, sys, json

def random_graph(n, p, rng):
    A = (rng.random((n, n)) < p).astype(float)
    A = np.triu(A, 1)
    A = A + A.T
    return A

def iterate(B, x0, steps, record_every=1):
    x = np.array(x0, dtype=float)
    traj = []
    for k in range(steps):
        z = B @ x
        x = x / z
        if k % record_every == 0:
            traj.append(x.copy())
    return x, np.array(traj)

def osc_amplitude(B, x, tail=20000):
    """max deviation of direction over tail iterations from its window mean"""
    x, traj = iterate(B, x, tail, record_every=10)
    # projective normalize
    traj = traj / traj.sum(axis=1, keepdims=True)
    mean = traj.mean(axis=0)
    dev = np.abs(traj - mean).max()
    return dev, traj[-1], mean

def main():
    rng = np.random.default_rng(7)
    worst = []
    trials = 0
    for n in [3,4,5,6,7,8]:
        for trial in range(400):
            p = rng.uniform(0.15, 0.8)
            A = random_graph(n, p, rng)
            # ensure connected
            if n > 1:
                seen = {0}; stack=[0]; Ad=A>0
                while stack:
                    v = stack.pop()
                    for w in range(n):
                        if Ad[v,w] and w not in seen:
                            seen.add(w); stack.append(w)
                if len(seen) < n: continue
            B = A + np.eye(n)
            for s in range(3):
                x0 = np.exp(rng.uniform(-4, 4, size=n))
                dev, xend, mean = osc_amplitude(B, x0)
                trials += 1
                worst.append((dev, n, A.copy(), x0, xend))
    worst.sort(key=lambda t: -t[0])
    print(f"trials={trials}")
    for dev, n, A, x0, xend in worst[:8]:
        print(f"dev={dev:.3e} n={n}")
        print("  A=", A.astype(int).tolist())
        print("  x0=", np.round(x0,4).tolist())
        print("  xend_dir=", np.round(xend,6).tolist())
    json.dump({"trials": trials,
               "top": [(float(w[0]), w[1], w[2].astype(int).tolist(), np.round(w[3],6).tolist()) for w in worst[:20]]},
              open("convergence-search.json","w"), indent=1)

if __name__ == "__main__":
    main()
