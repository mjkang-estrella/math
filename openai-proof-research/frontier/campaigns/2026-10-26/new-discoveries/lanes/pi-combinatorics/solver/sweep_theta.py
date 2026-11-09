#!/usr/bin/env python3
"""Sweep theta graphs Theta(j,k,l): winner vs parity of total edges.
Reports any violation of: odd edges -> P1, even edges -> P2 (min degree >= 2 boards).
"""
import gen, sys

def main(maxtotal=16):
    viols = []
    results = {}
    for j in range(1, maxtotal):
        for k in range(j, maxtotal):
            for l in range(k, maxtotal):
                tot = j + k + l
                if tot > maxtotal: continue
                for outer in range(3):
                    text = gen.theta_board(j, k, l, outer=outer)
                    w = gen.solve(text)
                    pred = "P1" if tot % 2 == 1 else "P2"
                    key = (j, k, l, outer)
                    results[key] = w
                    if w != pred:
                        viols.append((key, tot, w, pred))
                        print(f"VIOLATION Theta({j},{k},{l}) outer={outer}: edges={tot} ({'odd' if tot%2 else 'even'}), winner={w}, parity predicts {pred}")
    print(f"checked {len(results)} boards (j<=k<=l, total<={maxtotal}), {len(violations) if False else len(viols)} violations")
    # dump results table for proof extraction
    import json
    json.dump({str(k): v for k, v in results.items()}, open('theta_results.json', 'w'))

if __name__ == '__main__':
    mt = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    main(mt)
