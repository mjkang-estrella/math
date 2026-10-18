# Reviewer coverage search for host/flip/reclassification branches (rcs128-proof-r1). SPDX-License-Identifier: MIT
"""Random + mutation search for inputs exercising requests, splices and reflected
batch reclassification in the reviewer's executable model.  Any assertion
failure is printed with its input.  Finite diagnostics only."""
import json, random, sys, traceback
from collections import Counter
from rc_algorithm import solve, Fail
from run_algorithm_search import INV, gen, gen_nested, gen_req
from rc_counts import make_rho

def mutate(rng, words, cm):
    al = sorted(cm); rho = make_rho(cm); w = list(words)
    op = rng.randrange(5)
    i = rng.randrange(len(w))
    s = w[i]
    if op == 0 and len(s) > 2:
        j = rng.randrange(len(s)); w[i] = s[:j] + s[j+1:]
    elif op == 1:
        j = rng.randrange(len(s)+1); w[i] = s[:j] + rng.choice(al) + s[j:]
    elif op == 2:
        w[i] = rho(s)
    elif op == 3 and len(w) < 6:
        a = rng.randrange(len(s)); w.append(s[a:] + s[:a] + rng.choice(al))
    elif op == 4 and len(w) > 1:
        w.pop(i)
    return [x for x in w if len(x) <= 18] or words

def score(log):
    return 10*log.get('reclass2',0)+10*log.get('reclass3',0)+5*log.get('splices',0)+3*log.get('host_applications',0)+log.get('requests',0)

def main(seed, rounds):
    rng = random.Random(seed); tot = Counter(); pool = []; examples = []
    for r in range(rounds):
        if pool and rng.randrange(3):
            words, cm = rng.choice(pool); words = mutate(rng, words, cm)
        else:
            cm = INV[r % len(INV)]; words = [gen, gen_nested, gen_req][r % 3](rng, cm)
        ts = rng.randrange(10**6)
        try:
            T, M = solve(words, cm, ts)
        except Fail as e:
            print(json.dumps(dict(kind='ASSERTION', msg=str(e), words=words, cm=cm, seed=ts))); return 1
        except Exception:
            print(json.dumps(dict(kind='CRASH', words=words, cm=cm, seed=ts, tb=traceback.format_exc()))); return 2
        sc = score(M.log); tot.update(M.log)
        if sc > 0:
            pool.append((words, cm))
            if len(examples) < 12 and (M.log.get('reclass2') or M.log.get('reclass3') or M.log.get('splices')):
                examples.append(dict(words=words, cm=cm, seed=ts, log=dict(M.log)))
    tot.pop('max_cycle_len', None)
    print(json.dumps(dict(seed=seed, rounds=rounds, coverage=dict(sorted(tot.items())), examples=examples,
                          meaning='no assertion failure in this bounded run; not a proof')))
    return 0

if __name__ == '__main__': sys.exit(main(int(sys.argv[1]), int(sys.argv[2])))
