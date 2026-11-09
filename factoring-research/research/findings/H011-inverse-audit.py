#!/usr/bin/env python3
"""H011 exact affine-residue reporter and frozen correctness audit.

No factoring library, supplied factors, external oracle, or imported lab code.
The slow direct-inverse reference is called by the audit only.
"""
import hashlib
import json
import math
from pathlib import Path
import signal
import time

BASE = Path(__file__).resolve().parent
PREFIX = "H011-inverse-"


class Deadline(Exception):
    pass


class Meter:
    def __init__(self, deadline):
        self.deadline = deadline
        self.counts = {}

    def tick(self, name, count=1):
        self.counts[name] = self.counts.get(name, 0) + count
        if time.monotonic() >= self.deadline:
            raise Deadline("cooperative deadline")


def floor_sum(n, m, a, b, meter):
    """Sum floor((a*i+b)/m), 0<=i<n; exact signed Euclidean recursion."""
    meter.tick("floor_sum_calls")

    def rec(n, m, a, b):
        meter.tick("euclidean_steps")
        if n == 0:
            return 0
        qa, a = divmod(a, m)
        qb, b = divmod(b, m)
        ans = qa * n * (n - 1) // 2 + qb * n
        if a == 0:
            return ans
        t = (a * (n - 1) + b) // m
        if t == 0:
            return ans
        return ans + t * n - rec(t, a, m, m - b + a - 1)

    assert n >= 0 and m > 0
    return rec(n, m, a, b)


def affine_count(left, right, h, c, modulus, ylo, yhi, meter):
    meter.tick("count_queries")
    if left > right or ylo > yhi:
        return 0
    assert 0 <= ylo <= yhi < modulus
    n = right - left + 1
    b = c + h * left
    return (floor_sum(n, modulus, h, b - ylo, meter)
            - floor_sum(n, modulus, h, b - yhi - 1, meter))


def ceil_div(a, b):
    return -((-a) // b)


def report(N, s, I, J, meter):
    """Stream all ordered pairs in the given public box with pq=N mod R^5."""
    R = 1 << s
    M = 1 << (5 * s)
    r = (5 * s) // 2
    D = 1 << r
    H = M // D
    assert s >= 2 and N % 2 == 1
    if I[0] > I[1] or J[0] > J[1]:
        return
    assert R**3 // 2 <= I[0] <= I[1] < R**3
    assert R**3 // 2 <= J[0] <= J[1] < R**3
    for a in range(1, D, 2):
        meter.tick("patches_considered")
        xlo = ceil_div(I[0] - a, D)
        xhi = (I[1] - a) // D
        if xlo > xhi:
            continue
        meter.tick("modular_inverses", 2)
        v = N * pow(a, -1, M) % M
        v1 = N * pow(a + D, -1, M) % M
        b = v % D
        delta = (v1 - v) % M
        assert delta % D == 0
        c, h = (v - b) // D, delta // D
        ylo = ceil_div(J[0] - b, D)
        yhi = (J[1] - b) // D
        if ylo > yhi:
            continue
        meter.tick("nonempty_coordinate_boxes")
        total = affine_count(xlo, xhi, h, c, H, ylo, yhi, meter)
        stack = [(xlo, xhi, total)]
        while stack:
            left, right, count = stack.pop()
            meter.tick("report_nodes")
            if count == 0:
                continue
            if left == right:
                assert count == 1
                p = a + D * left
                q = b + D * ((c + h * left) % H)
                assert I[0] <= p <= I[1] and J[0] <= q <= J[1]
                assert (p * q - N) % M == 0
                meter.tick("reported_pairs")
                yield p, q
                continue
            mid = (left + right) // 2
            lcount = affine_count(left, mid, h, c, H, ylo, yhi, meter)
            assert 0 <= lcount <= count
            stack.append((mid + 1, right, count - lcount))
            stack.append((left, mid, lcount))


def direct_reference(N, s, I, J, meter):
    """Audit-only exhaustive inverse enumeration, fully charged separately."""
    M = 1 << (5 * s)
    pairs = []
    for p in range(I[0] | 1, I[1] + 1, 2):
        meter.tick("reference_p_checks")
        q = N * pow(p, -1, M) % M
        if J[0] <= q <= J[1]:
            pairs.append((p, q))
    return pairs


def make_cases():
    cases = [dict(id="signed-floor-sums", kind="floor")]
    for s in (2, 3, 4, 5):
        R = 1 << s
        B = R**6
        for j, N in enumerate((B // 4 + 1, 5 * B // 16 + 1, 3 * B // 8 - 1)):
            cases.append(dict(id=f"affine-{s}-{j}",kind="affine",s=s,N=N))
            full = [R**3 // 2, R**3 - 1]
            clipI = [full[0], min(full[1], math.isqrt(N))]
            clipJ = [max(full[0], ceil_div(N, R**3)), min(full[1], 2*N // R**3)]
            for name, I, J in (
                ("full", full, full),
                ("clipped-balanced", clipI, clipJ),
                ("singleton", [full[0] + 1, full[0] + 1], full),
                ("empty", [full[0], full[0] - 1], full),
            ):
                cases.append(dict(id=f"report-{s}-{j}-{name}",kind="report",s=s,N=N,I=I,J=J))
    return cases


def audit_case(case, meter):
    kind = case["kind"]
    if kind == "floor":
        for n in range(9):
            for m in range(1, 18):
                for a in range(-17, 18):
                    for b in range(-19, 20):
                        meter.tick("floor_cases")
                        got = floor_sum(n, m, a, b, meter)
                        want = sum((a*i+b)//m for i in range(n))
                        if got != want:
                            raise AssertionError(dict(n=n,m=m,a=a,b=b,got=got,want=want))
        return {}
    s, N = case["s"], case["N"]
    if kind == "affine":
        M = 1 << (5*s)
        rstar = (5*s)//2
        for r in (rstar-1, rstar):
            D = 1 << r
            for a in range(1, D, 2):
                meter.tick("affine_cases")
                vals = [N*pow(a+D*x,-1,M)%M for x in range(3)]
                delta2 = (vals[2]-2*vals[1]+vals[0]) % M
                expected_gcd = 1 << min(2*r+1,5*s)
                if math.gcd(delta2,M) != expected_gcd:
                    raise AssertionError(dict(r=r,a=a,delta2=delta2,expected_gcd=expected_gcd))
                assert (delta2 == 0) == (r == rstar)
        return {}
    I, J = case["I"], case["J"]
    got = list(report(N,s,I,J,meter))
    # Reporting has completed before any exhaustive reference is available.
    want = direct_reference(N,s,I,J,meter)
    assert len(got) == len(set(got)), "duplicate output"
    assert sorted(got) == want, dict(got=sorted(got),want=want)
    if case["id"].endswith("-full"):
        expected_patches = 1 << ((5*s)//2 - 1)
        assert meter.counts["patches_considered"] == expected_patches
        assert meter.counts["nonempty_coordinate_boxes"] == expected_patches
    return dict(pairs=sorted(got),actual_factor_pairs=[pair for pair in sorted(got) if pair[0]*pair[1]==N])


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    start = time.monotonic()
    protocol_path = BASE / (PREFIX + "protocol.json")
    protocol = json.loads(protocol_path.read_text())
    source_hash = sha(Path(__file__))
    assert source_hash == protocol["source_sha256"], "source was changed after freeze"
    deadline = start + protocol["cooperative_cap_seconds"]
    cases = make_cases()
    assert len(cases) == protocol["total_cases"]
    result_path = BASE / (PREFIX + "results.json")
    event_path = BASE / (PREFIX + "events.jsonl")
    cases_path = BASE / (PREFIX + "cases.json")
    for path in (result_path,event_path,cases_path):
        if path.exists():
            raise FileExistsError("preserving previous evidence: " + str(path))
    with cases_path.open("x") as f:
        json.dump(cases,f,indent=2)
        f.write("\n")
    rows = [dict(case=case,status="unstarted") for case in cases]
    hashes = dict(source_sha256=source_hash,protocol_sha256=sha(protocol_path),cases_sha256=sha(cases_path))

    def stop(signum, frame):
        raise Deadline("outer signal " + str(signum))

    signal.signal(signal.SIGTERM,stop)
    with event_path.open("x", buffering=1) as events:
        def event(obj):
            events.write(json.dumps(obj,sort_keys=True)+"\n")
            events.flush()

        event(dict(kind="freeze",hashes=hashes,total_cases=len(cases)))
        try:
            for row in rows:
                if time.monotonic() >= deadline:
                    break
                case_start = time.monotonic()
                meter = Meter(deadline)
                row["status"] = "started"
                event(dict(kind="started",case=row["case"]))
                try:
                    row.update(audit_case(row["case"],meter))
                    row["status"] = "passed"
                except Deadline as err:
                    row.update(status="deadline",error=str(err))
                except Exception as err:
                    row.update(status="failed",error=repr(err))
                row["counts"] = meter.counts
                row["seconds"] = time.monotonic()-case_start
                event(dict(kind="result",**row))
                if row["status"] in ("failed","deadline"):
                    break
        finally:
            # Unstarted cases remain explicit. JSONL also survives a hard kill.
            result = dict(hashes=hashes,seconds=time.monotonic()-start,
                          cases=rows,protocol=protocol,
                          scope="correctness audit only; no performance inference")
            with result_path.open("x") as f:
                json.dump(result,f,indent=2)
                f.write("\n")
    summary = {status:sum(row["status"]==status for row in rows)
               for status in ("passed","failed","deadline","unstarted","started")}
    print(json.dumps(dict(summary=summary,seconds=result["seconds"],hashes=hashes),indent=2))


if __name__ == "__main__":
    main()
