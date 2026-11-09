"""W022-B review certificate. Exact-integer verifier; NOT a factoring algorithm."""
import json, math, sys, time, hashlib

CAP = 20000
T0 = time.time()
events = 0
max_comb_bits = 0

class Cap(Exception):
    pass

def ch(k=1):
    global events
    if events + k > CAP:
        raise Cap()
    if time.time() - T0 > 55:
        raise Cap()
    events += k

def comb(a, b):
    global max_comb_bits
    ch()
    v = math.comb(a, b)
    max_comb_bits = max(max_comb_bits, v.bit_length())
    return v

def gcd(a, b):
    ch(); return math.gcd(a, b)

def H_at_minus1_and_deriv(n):
    """Exact H_n(-1), H_n'(-1) from the defining sum."""
    h = 0; d = 0
    for j in range(n + 1):
        c = comb(n, j); ch(); c2 = c * c
        s = -1 if j % 2 else 1
        ch(); h += s * c2
        if j:
            ch(2); d += (-s) * j * c2   # (-1)^(j-1) = -(-1)^j
    return h, d

def H_minus1_closed(n):
    # exact closed form used only for small Lucas factors
    if n % 2: return 0
    return (-1) ** (n // 2) * comb(n, n // 2)

def H_deriv_closed(n):
    # valid for odd n: (-1)^m n C(2m,m), n=2m+1
    m = (n - 1) // 2
    ch()
    return (-1) ** m * n * comb(2 * m, m)

def lucas_termwise(n, l):
    bad = 0
    for j in range(n + 1):
        a = comb(n, j); ch(); a = (a * a) % l
        b = comb(n % l, j % l) if j % l <= n % l else 0
        c = comb(n // l, j // l) if j // l <= n // l else 0
        ch(2); r = (b * b * c * c) % l
        ch()
        if a != r: bad += 1
    return bad

proto = json.load(open(sys.argv[1]))
results = []
def rec(**kw): results.append(kw)

try:
    groups = [("close", proto["cases_semiprime_p3_q1_close_q_lt_2p"]),
              ("unbalanced", proto["cases_semiprime_p3_q1_unbalanced_q_gt_2p"])]
    for gname, cases in groups:
        for p, q in cases:
            r = dict(group=gname, p=p, q=q, status="unstarted"); results.append(r)
            N = p * q
            assert p % 4 == 3 and q % 4 == 1 and p != q
            r.update(N=N, status="started")
            m = (N - 3) // 4; n = 2 * m + 1
            B = comb(2 * m, m)
            r["central_bits"] = B.bit_length()
            g = gcd(B, N)                       # selector: uses N only
            r["gcd"] = g
            pdiv = comb((q - 1) // 2, (q - 1) // 4) % p == 0; ch()
            pred = N if pdiv else q
            r["pred_gcd"] = pred; r["P1_ok"] = (g == pred)
            r["q_lt_2p"] = q < 2 * p
            # P3 derivative mod p via Lucas factors, and mod q zero
            D = H_deriv_closed(n)
            lhs_p = D % p; ch()
            rhs_p = (H_deriv_closed((p - 1) // 2) * H_minus1_closed((q - 1) // 2)) % p; ch()
            r["P3_derivmod_p_ok"] = (lhs_p == rhs_p); r["deriv_mod_p_nonzero"] = lhs_p != 0
            ch(); r["P3_derivmod_q_zero"] = (D % q == 0)
            if N <= 700:
                h, d = H_at_minus1_and_deriv(n)
                r["P2_H_minus1_zero"] = (h == 0); r["P2_deriv_ok"] = (d == D)
            if N <= 400:
                r["P3_lucas_bad_terms_p"] = lucas_termwise(n, p)
                r["P3_lucas_bad_terms_q"] = lucas_termwise(n, q)
            r["status"] = "done"
    for p, q in proto["cases_N1mod4_negative_controls"]:
        r = dict(group="N1mod4", p=p, q=q, status="unstarted"); results.append(r)
        N = p * q; r.update(N=N, status="started")
        r["selector_defined"] = (N - 3) % 4 == 0
        A = comb((N - 1) // 2, (N - 1) // 4)
        r["analog_bits"] = A.bit_length()
        g = gcd(A, N); r["analog_gcd"] = g
        pred = 1
        for l, c in ((p, q), (q, p)):
            if l % 4 == 3: pred *= l
            elif comb((c - 1) // 2, (c - 1) // 4) % l == 0: pred *= l
        ch()
        r["pred_prime_part"] = pred
        r["P4_ok"] = all((g % l == 0) == (pred % l == 0) for l in (p, q))
        r["status"] = "done"
    for fs in proto["cases_nonsemiprime_N3mod4"]:
        r = dict(group="nonsemiprime", factors=fs, status="unstarted"); results.append(r)
        N = math.prod(fs); r.update(N=N, status="started")
        assert N % 4 == 3
        B = comb((N - 3) // 2, (N - 3) // 4); g = gcd(B, N)
        r["gcd"] = g; ok = True; detail = {}
        for l in sorted(set(fs)):
            if l % 4 == 1: pr = True
            else:
                c = N // l; pr = comb((c - 1) // 2, (c - 1) // 4) % l == 0; ch()
            act = B % l == 0; ch()
            detail[str(l)] = dict(pred=pr, actual=act); ok &= (pr == act)
        r["P5_detail"] = detail; r["P5_ok"] = ok; r["status"] = "done"
except Cap:
    capped = True
else:
    capped = False

out = dict(events=events, cap=CAP, capped=capped, seconds=round(time.time() - T0, 3),
           max_comb_output_bits=max_comb_bits, results=results,
           python=sys.version.split()[0])
json.dump(out, open(sys.argv[2], "w"), indent=1)
print(json.dumps(dict(events=events, capped=capped, seconds=out["seconds"], n=len(results))))
