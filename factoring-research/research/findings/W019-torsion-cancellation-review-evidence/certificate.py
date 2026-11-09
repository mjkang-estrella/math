"""W019-B single-run certificate. See preregistration.md. Standard library only."""
import itertools
import json
import math
import sys
import time

EVENT_BUDGET = 20000
T0 = time.monotonic()


class Abort(Exception):
    pass


class Meter:
    def __init__(self):
        self.events = 0

    def tick(self, k=1):
        self.events += k
        if self.events > EVENT_BUDGET:
            raise Abort("event budget exceeded")


METER = Meter()


# ---------------- Part I: abstract abelian 2-groups ----------------

class Group:
    def __init__(self, exps):
        self.exps = tuple(exps)
        self.mods = tuple(2 ** e for e in exps)
        self.zero = tuple(0 for _ in exps)
        self.elements = list(itertools.product(*[range(m) for m in self.mods]))
        self.order = len(self.elements)

    # metered algorithm operations
    def dbl(self, x):
        METER.tick()
        return tuple((2 * xi) % m for xi, m in zip(x, self.mods))

    def sub(self, x, y):
        METER.tick()
        return tuple((xi - yi) % m for xi, yi, m in zip(x, y, self.mods))

    # unmetered verifier helpers
    def add_v(self, x, y):
        return tuple((xi + yi) % m for xi, yi, m in zip(x, y, self.mods))

    def mul_v(self, k, x):
        return tuple((k * xi) % m for xi, m in zip(x, self.mods))

    def log_order_v(self, x):
        t = 0
        while x != self.zero:
            x = self.mul_v(2, x)
            t += 1
        return t

    def top_v(self, x):
        t = self.log_order_v(x)
        return None if t == 0 else self.mul_v(2 ** (t - 1), x)

    def span_v(self, gens):
        S = {self.zero}
        frontier = [self.zero]
        while frontier:
            nxt = []
            for s in frontier:
                for g in gens:
                    y = self.add_v(s, g)
                    if y not in S:
                        S.add(y)
                        nxt.append(y)
            frontier = nxt
        return S

    def is_cyclic_v(self, S):
        invols = [x for x in S if x != self.zero and self.mul_v(2, x) == self.zero]
        return len(invols) <= 1


def power_table(G, x):
    """Metered: returns [x, 2x, 4x, ..., 2^(t-1)x] and t = log2 ord(x)."""
    table = []
    y = x
    while y != G.zero:
        table.append(y)
        y = G.dbl(y)
    return table, len(table)


def cancel(G, A, B):
    """W019 (B1) with swap. Returns (result, ops); result is an involution or None."""
    start = METER.events
    TA, s = power_table(G, A)
    J = TA[s - 1]
    if B == G.zero:
        return None, METER.events - start
    TB, t = power_table(G, B)
    Z = TB[t - 1]
    if Z != J:
        return Z, METER.events - start
    if t > s:
        TA, TB, s, t = TB, TA, t, s
        B = TB[0]
    while True:
        B = G.sub(B, TA[s - t])
        if B == G.zero:
            return None, METER.events - start
        TB, t = power_table(G, B)
        Z = TB[t - 1]
        if Z != J:
            return Z, METER.events - start


def part1():
    out = {"groups": [], "assertions": {}, "failures": []}
    fail = out["failures"]
    groups = [[1], [3], [1, 1], [1, 2], [2, 2], [1, 3], [1, 1, 1]]
    tables = {}
    for exps in groups:
        G = Group(exps)
        res = {}
        for A in G.elements:
            if A == G.zero:
                continue
            J = G.top_v(A)
            for B in G.elements:
                Z, ops = cancel(G, A, B)
                span = G.span_v([A, B])
                cyc = G.is_cyclic_v(span)
                m = max(G.log_order_v(A), G.log_order_v(B))
                # I1
                if Z is not None:
                    if not (G.mul_v(2, Z) == G.zero and Z != G.zero and Z != J and Z in span):
                        fail.append(["I1", exps, A, B, Z])
                # I2
                if (Z is not None) != (not cyc):
                    fail.append(["I2", exps, A, B, Z, cyc])
                # I3
                if ops > m * (m + 5) // 2:
                    fail.append(["I3", exps, A, B, ops, m])
                res[(A, B)] = (Z is not None, ops)
        tables[tuple(exps)] = (G, res)
        out["groups"].append({"exps": exps, "order": G.order, "runs": len(res),
                              "max_ops": max(o for _, o in res.values())})

    # I4, I6 and reported pivot-distribution (table lookups only; no new events)
    i4, i6, reported = [], [], []
    for exps, (G, res) in tables.items():
        if len(exps) < 2:
            continue
        expo = max(exps)
        for A in G.elements:
            if A == G.zero:
                continue
            sA = G.log_order_v(A)
            succ = sum(1 for B in G.elements if res[(A, B)][0])
            if sA == expo:
                idx = G.order // len(G.span_v([A]))
                ok = (succ * idx == G.order * (idx - 1)) and 2 * succ >= G.order
                i4.append([list(exps), list(A), succ, G.order, idx, ok])
                if not ok:
                    fail.append(["I4", exps, A, succ, idx])
            # I6: two samples with pivot upgrade
            total = 0
            for B1 in G.elements:
                if res[(A, B1)][0]:
                    total += G.order
                    continue
                P = B1 if G.log_order_v(B1) > sA else A
                total += sum(1 for B2 in G.elements if res[(P, B2)][0])
            frac = total / G.order ** 2
            i6.append([list(exps), list(A), frac])
            if 4 * total < G.order ** 2:
                fail.append(["I6", exps, A, frac])
        invols = [x for x in G.elements if x != G.zero and G.mul_v(2, x) == G.zero]
        for J in invols:
            pivots = [A for A in G.elements if A != G.zero and G.top_v(A) == J]
            canc = sum(1 for A in pivots for B in G.elements if res[(A, B)][0])
            naive = sum(1 for B in G.elements if B != G.zero and G.top_v(B) != J)
            reported.append({"exps": list(exps), "J": list(J), "num_pivots": len(pivots),
                             "P_cancel_uniform_pivot_with_top_J": canc / (len(pivots) * G.order),
                             "P_naive_chain": naive / G.order})
    out["I4_rows"] = i4
    out["I6_min_fraction"] = min(r[2] for r in i6)
    out["I6_rows"] = i6
    out["reported_pivot_model"] = reported

    # I5 counterexample family
    i5 = []
    for k in range(1, 6):
        G = Group([1, k])
        J = (0, 2 ** (k - 1))
        succ = 0
        for B in G.elements:
            Z, ops = cancel(G, J, B)
            succ += Z is not None
        naive = sum(1 for B in G.elements if B != G.zero and G.top_v(B) != J)
        i5.append({"k": k, "order": G.order, "cancel_success": succ, "naive_success": naive})
        if succ != 2 or naive != 2:
            fail.append(["I5", k, succ, naive])
    out["I5_rows"] = i5
    for name in ["I1", "I2", "I3", "I4", "I5", "I6"]:
        out["assertions"][name] = not any(f[0] == name for f in fail)
    return out


# ---------------- Part II: binary quadratic forms ----------------

def xgcd(a, b):
    x0, y0, x1, y1 = 1, 0, 0, 1
    while b:
        q, a, b = a // b, b, a % b
        x0, x1 = x1, x0 - q * x1
        y0, y1 = y1, y0 - q * y1
    return a, x0, y0


def reduce_form(a, b, c):
    while True:
        if not (-a < b <= a):
            # normalize b into (-a, a]
            k = (a - b) // (2 * a)
            c = c + b * k + a * k * k
            b = b + 2 * a * k
            continue
        if a > c:
            a, b, c = c, -b, a
            continue
        if a == c and b < 0:
            b = -b
        return (a, b, c)


def compose(f, g, D):
    METER.tick()
    a1, b1, c1 = f
    a2, b2, c2 = g
    h = (b1 + b2) // 2
    d0, u0, v0 = xgcd(a1, a2)
    e, x, w = xgcd(d0, h)  # e = x*d0 + w*h
    u, v = x * u0, x * v0  # e = u*a1 + v*a2 + w*h
    A3 = a1 * a2 // (e * e)
    B3 = (u * a1 * b2 + v * a2 * b1 + w * (b1 * b2 + D) // 2) // e
    B3 %= 2 * A3
    ok = (B3 * B3 - D) % (4 * A3) == 0
    C3 = (B3 * B3 - D) // (4 * A3) if ok else None
    return (A3, B3, C3), ok


def reduced_forms(D):
    forms = []
    a = 1
    while 3 * a * a <= -D:
        for b in range(-a + 1, a + 1):
            if (b - D) % 2:
                continue
            if (b * b - D) % (4 * a):
                continue
            c = (b * b - D) // (4 * a)
            if c < a or (c == a and b < 0):
                continue
            if math.gcd(math.gcd(a, b), c) != 1:
                continue
            forms.append((a, b, c))
        a += 1
    return forms


def is_prime(n):
    return n > 1 and all(n % r for r in range(2, int(math.isqrt(n)) + 1))


def part2():
    out = {"cases": [], "assertions": {}, "failures": []}
    fail = out["failures"]
    for N in range(15, 400, 2):
        fac = [p for p in range(3, int(math.isqrt(N)) + 1) if N % p == 0 and is_prime(p)]
        if not fac:
            continue
        p = fac[0]
        q = N // p
        if q == p or not is_prime(q):
            continue
        D = -4 * N if N % 4 == 1 else -N
        forms = reduced_forms(D)
        principal = (1, 0, N) if D % 4 == 0 else (1, 1, (N + 1) // 4)
        amb = []
        for f in forms:
            sq, ok = compose(f, f, D)
            if not ok:
                fail.append(["II1", N, f])
                continue
            if reduce_form(*sq) == principal:
                amb.append(f)
        if D % 4 == 0:
            X = (2 * p, 2 * p, (p + q) // 2) if q > 3 * p else ((p + q) // 2, q - p, (p + q) // 2)
            pred = {(1, 0, N), (p, 0, q), (2, 2, (N + 1) // 2), X}
            J = (2, 2, (N + 1) // 2)
            want = 4
        else:
            Y = (p, p, (p + q) // 4) if q > 3 * p else ((p + q) // 4, (q - p) // 2, (p + q) // 4)
            pred = {(1, 1, (N + 1) // 4), Y}
            J = None
            want = 2
        if len(amb) != want:
            fail.append(["II2", N, amb])
        if set(amb) != pred:
            fail.append(["II3", N, sorted(amb), sorted(pred)])
        divs = {}
        for (a, b, c) in amb:
            if b == 0:
                d = a
            elif b == a:
                d = a // 2 if D % 4 == 0 else a
            elif a == c:
                d = a - b // 2 if D % 4 == 0 else 2 * a - b
            else:
                fail.append(["II4", N, (a, b, c)])
                continue
            divs[str((a, b, c))] = d
            trivial = (a, b, c) == principal or (a, b, c) == J
            if trivial and d != 1:
                fail.append(["II5", N, (a, b, c), d])
            if not trivial and d not in (p, q):
                fail.append(["II5", N, (a, b, c), d])
        out["cases"].append({"N": N, "p": p, "q": q, "D": D, "h": len(forms),
                             "ambiguous": [list(f) for f in amb], "divisors": divs})
    for name in ["II1", "II2", "II3", "II4", "II5"]:
        out["assertions"][name] = not any(f[0] == name for f in fail)
    return out


def main():
    result = {"status": "started"}
    try:
        result["part1"] = part1()
        result["events_after_part1"] = METER.events
        result["part2"] = part2()
        result["status"] = "completed"
    except Abort as exc:
        result["status"] = "aborted: " + str(exc)
    result["events_total"] = METER.events
    result["event_budget"] = EVENT_BUDGET
    result["elapsed_s"] = time.monotonic() - T0
    allok = result["status"] == "completed" and all(
        v for part in ("part1", "part2") for v in result[part]["assertions"].values())
    result["all_assertions_pass"] = allok
    json.dump(result, sys.stdout, indent=1, default=list)
    sys.stdout.write("\n")


if __name__ == "__main__":
    main()
