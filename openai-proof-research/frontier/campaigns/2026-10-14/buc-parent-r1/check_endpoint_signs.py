#!/usr/bin/env python3
"""MIT. Exhaustive small sign averages; not a universal mathematical proof."""
from fractions import Fraction
from itertools import combinations, product
import json


def check():
    count = 0
    for n in range(1, 6):
        possible = list(combinations(range(n), 2))
        for mask in range(1 << len(possible)):
            edges = [e for j, e in enumerate(possible) if mask >> j & 1]
            active = {v for e in edges for v in e}
            todo = set(active)
            components = []
            while todo:
                component = {todo.pop()}
                stack = list(component)
                while stack:
                    u = stack.pop()
                    for a, b in edges:
                        v = b if a == u else a if b == u else None
                        if v is not None and v not in component:
                            component.add(v)
                            todo.discard(v)
                            stack.append(v)
                components.append(component)
            valid = all(sum(u in c for u, v in edges) % 2 == 0
                        for c in components)
            predicted = (Fraction(2) ** (len(components) - len(active))
                         if valid else Fraction(0))
            total = 0
            for signs in product([-1, 1], repeat=n):
                term = 1
                for u, v in edges:
                    term *= (signs[u] + signs[v]) // 2
                total += term
            assert Fraction(total, 2 ** n) == predicted
            count += 1
    return count


if __name__ == '__main__':
    print(json.dumps({'status': 'PASS_FINITE_DIAGNOSTIC_ONLY', 'graphs': check()}))
