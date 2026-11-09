"""Construct valid degree-five relaxed witnesses; never infer infeasibility."""
import hashlib
import json
import math
import platform
import random
import statistics
import time
from collections import Counter
from pathlib import Path

CONFIG = {"K": [12, 18, 24, 30, 36], "samples": 4, "seed": 6006,
          "internal_seconds": 55, "reject_fraction": 0.5}


def bounds(j, t, lo, hi):
    low = max(lo**j + j * lo**(j-1) * (t-lo),
              hi**j + j * hi**(j-1) * (t-hi))
    high = ((hi-t)*lo**j + (t-lo)*hi**j) // (hi-lo)
    return low, high


def certificate(n, k, s, a, lo, hi, c, qlo, qhi, counts):
    modulus, radix = 1 << k, 1 << s
    if lo == hi:
        q = sum(c[j] * lo**j for j in range(6)) % modulus
        return (lo, q, [lo**j for j in range(6)]) if qlo <= q <= qhi else None
    candidates = dict.fromkeys(((lo+hi)//2, lo+1, hi-1))
    for t in candidates:
        if not lo < t < hi:
            continue
        counts["interior_t_attempts"] += 1
        z = [1, t, t*t]
        partial = sum(c[j]*z[j] for j in range(3))
        q = qlo + ((partial-qlo) % radix**3)
        if q > qhi:
            continue
        for j in range(3, 6):
            assert (q-partial) % radix**j == 0
            residue = ((q-partial)//radix**j * pow(c[j]//radix**j, -1, radix)) % radix
            lower, upper = bounds(j, t, lo, hi)
            value = lower + ((residue-lower) % radix)
            if value > upper:
                break
            z.append(value)
            partial += c[j]*value
        if len(z) != 6:
            continue
        assert (sum(c[j]*z[j] for j in range(6))-q) % modulus == 0
        assert qlo <= q <= qhi and lo <= t <= hi and z[2] == t*t
        assert all(bounds(j,t,lo,hi)[0] <= z[j] <= bounds(j,t,lo,hi)[1] for j in range(2,6))
        counts["peak_certificate_bits"] = max(counts["peak_certificate_bits"],
                                              max(abs(v).bit_length() for v in z), abs(partial).bit_length())
        return t, q, z
    return None


def probe(n, k, deadline):
    s, modulus = k//6, 1 << k
    radix = 1 << s
    lower, upper = 1 << (k//2-1), (1 << (k//2))-1
    counts = Counter()
    start = time.monotonic()
    full_nodes = 0
    status = "complete"
    for a in range(1, radix, 2):
        lo, hi = max(0, (lower-a+radix-1)//radix), (upper-a)//radix
        if lo > hi:
            continue
        full_nodes += 2*(hi-lo+1)-1
    for a in range(1, radix, 2):
        lo, hi = max(0, (lower-a+radix-1)//radix), (upper-a)//radix
        if lo > hi:
            continue
        inv = pow(a,-1,modulus)
        c = [n * (-1)**j * pow(inv,j+1,modulus) * radix**j % modulus for j in range(6)]
        stack = [(lo,hi,0)]
        while stack:
            if time.monotonic() >= deadline:
                status = "partial"
                break
            left,right,depth = stack.pop()
            counts["visited_nodes"] += 1
            witness = certificate(n,k,s,a,left,right,c,lower,upper,counts)
            if witness is None:
                counts["uncertified_boundary_nodes"] += 1
                continue
            t,q,z = witness
            counts["certified_nodes"] += 1
            assert sum(c[j]*t**j for j in range(6)) % modulus == n*pow(a+radix*t,-1,modulus)%modulus
            if (a+radix*t)*q != n:
                counts["spurious_certificates"] += 1
            else:
                counts["true_factor_certificates"] += 1
            if left != right:
                mid=(left+right)//2
                stack.extend(((mid+1,right,depth+1),(left,mid,depth+1)))
        if status != "complete":
            break
    return {"n":n,"K":k,"s":s,"status":status,"counts":dict(counts),
            "full_unpruned_nodes":full_nodes,
            "certified_subtree_node_fraction":counts["visited_nodes"]/full_nodes,
            "seconds":time.monotonic()-start}


def prime(n):
    return n>=2 and all(n%d for d in range(2,math.isqrt(n)+1))


def main():
    here=Path(__file__).resolve().parent
    output=here/'result.json'
    if output.exists():
        raise SystemExit('Refusing to overwrite existing evidence.')
    start=time.monotonic()
    deadline=start+CONFIG['internal_seconds']
    rng=random.Random(CONFIG['seed'])
    rows,generation=[],[]
    for k in CONFIG['K']:
        low,high=1<<(k//2-1),1<<(k//2)
        selected=[]
        attempts=0
        while len(selected)<CONFIG['samples'] and attempts<10000 and time.monotonic()<deadline:
            attempts+=1
            p,q=rng.randrange(low,high)|1,rng.randrange(low,high)|1
            if p!=q and prime(p) and prime(q):
                n=p*q
                if n.bit_length()==k-1 and n not in selected:
                    selected.append(n)
        generation.append({"K":k,"attempts":attempts,"selected_n":selected,
                           "sample_shortfall":CONFIG['samples']-len(selected)})
        for n in selected:
            rows.append(probe(n,k,deadline) if time.monotonic()<deadline
                        else {"n":n,"K":k,"status":"unstarted"})
    summaries=[]
    for k in CONFIG['K']:
        group=[r for r in rows if r['K']==k]
        done=[r for r in group if r['status']=='complete']
        summaries.append({"K":k,"status_counts":dict(Counter(r['status'] for r in group)),
                          "median_subtree_fraction":statistics.median(r['certified_subtree_node_fraction'] for r in done) if done else None,
                          "median_visited_nodes":statistics.median(r['counts']['visited_nodes'] for r in done) if done else None,
                          "spurious_certificates":sum(r['counts'].get('spurious_certificates',0) for r in done)})
    largest=next((r for r in reversed(summaries) if r['median_subtree_fraction'] is not None),None)
    disposition='inconclusive' if largest is None or largest['median_subtree_fraction']<CONFIG['reject_fraction'] else 'small_full_tree_hypothesis_empirically_unsupported'
    protocol=here.parents[1]/'hypotheses/H006.md'
    result={"schema":1,"config":CONFIG,"python":platform.python_version(),
            "source_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "protocol_sha256":hashlib.sha256(protocol.read_bytes()).hexdigest(),
            "seconds":time.monotonic()-start,"generation":generation,"rows":rows,
            "summaries":summaries,"disposition":disposition,
            "limitations":["certificate failure is inconclusive", "full-tree work, not early-stop factoring runtime", "finite data, not an asymptotic proof"]}
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({"summaries":summaries,"disposition":disposition,"seconds":result['seconds']}))


if __name__=='__main__':
    main()
