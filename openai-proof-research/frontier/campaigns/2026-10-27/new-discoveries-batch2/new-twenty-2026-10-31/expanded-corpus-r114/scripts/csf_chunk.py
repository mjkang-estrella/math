# Chunked CSF hashing for Conjecture 8.1 of arXiv:2505.06486 (MathDB 368352).
# usage: csf_chunk.py n c i m out.jsonl  -- processes compositions with index = i mod m;
# writes one JSON line per graph: sha256 of the canonical CSF (sorted (partition, coeff) list), seq, invariants.
import sys, os, json, hashlib, itertools
n, c, ci, cm, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
sys.argv = ['csf.py', str(n), str(c)]
__file__ = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'csf.py')
exec(open(__file__).read().split("if __name__")[0])
cnt = 0
with open(out, 'w') as fh:
    for idx, comp in enumerate(compositions(n, c)):
        if idx % cm != ci: continue
        for choice in itertools.product(*[range(len(trees[a])) for a in comp]):
            seq = tuple(zip(comp, choice))
            if canon(seq) != seq: continue
            h = hashlib.sha256(repr(sorted(csf(seq))).encode()).hexdigest()
            fh.write(json.dumps([h, repr(seq), invariants(seq)]) + '\n'); cnt += 1
print('chunk', ci, 'of', cm, 'graphs', cnt)
