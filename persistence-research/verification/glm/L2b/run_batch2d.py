# Batch-run Agent A's gen_nd for all alive 2-D (A,K) pairs.
import subprocess, os, json, sys, time

HERE = os.path.dirname(os.path.abspath(__file__))
INDEP = os.path.abspath(os.path.join(HERE, '..', '..', 'indep'))
OUTDIR = os.path.join(HERE, 'certs2d')
os.makedirs(OUTDIR, exist_ok=True)

# (A, K) alive pairs from configs.json census (2-far, one far digit)
PAIRS = [(9, 44), (9, 107), (9, 116), (9, 134), (9, 152), (9, 188), (9, 206), (9, 287), (9, 296), (9, 449), (9, 458), (9, 629), (9, 926), (9, 944), (9, 962), (9, 1007), (9, 1016), (9, 1088), (9, 1169), (9, 1178), (9, 1349), (9, 1529), (9, 1808), (9, 1889), (9, 1898), (9, 2069), (9, 2708), (9, 2726), (9, 2789), (9, 2969), (9, 4508), (9, 4589), (9, 6308), (9, 6389), (18, 44), (18, 98), (18, 107), (18, 116), (18, 143), (18, 188), (18, 269), (18, 449), (18, 548), (18, 629), (18, 908), (18, 926), (18, 989), (18, 1169), (18, 1808), (18, 1889), (18, 2708), (18, 2789), (18, 5408), (18, 5489), (27, 44), (27, 98), (27, 107), (27, 116), (27, 188), (27, 269), (27, 449), (27, 629), (27, 908), (27, 926), (27, 989), (27, 1169), (27, 1808), (27, 1889), (27, 2708), (27, 2789), (45, 8), (45, 89), (45, 98), (45, 269), (45, 908), (45, 989), (54, 8), (54, 44), (54, 89), (54, 107), (54, 188), (54, 449), (54, 1808), (54, 1889), (63, 8), (63, 89), (63, 98), (63, 269), (63, 908), (63, 989), (72, 8), (72, 89)]

def v2(k):
    n = 0
    while k % 2 == 0: k //= 2; n += 1
    return n

status = {}
for A, K in PAIRS:
    out = os.path.join(OUTDIR, f'nd2d_A{A}_K{K}.jsonl')
    if os.path.exists(out):
        status[f'{A},{K}'] = 'exists'; continue
    qmin = max(3, v2(K) + 1)
    cmd = f'ulimit -v 1500000; cd {HERE} cd {INDEP} && python3 -I gen_nd_L2.pycd {INDEP} && python3 -I gen_nd_L2.py python3 -I gen_nd_L2.py {out} 2 {A} {K} {qmin}'
    t0 = time.time()
    r = subprocess.run(['bash', '-c', cmd], capture_output=True, text=True)
    dt = time.time() - t0
    ok = 'solutions:' in r.stdout
    status[f'{A},{K}'] = f'rc={r.returncode} t={dt:.0f}s ' + r.stdout.strip().splitlines()[0] if r.stdout else f'rc={r.returncode} t={dt:.0f}s'
    print(status[f'{A},{K}'], flush=True)
    if r.returncode not in (0, 2):
        print('STDERR:', r.stderr[-2000:], flush=True)
json.dump(status, open(os.path.join(OUTDIR, 'batch_status.json'), 'w'), indent=1)
print('DONE')
