"""Post-write verifier for lane pi-restricted-stack-periodicity-hypothesis-r329.

Independently re-executed checks:
 1. Every file listed in manifest.json exists with exact sha256 and size.
 2. The on-disk payload set equals the manifest set, enumerating all files under
    the lane root and excluding ONLY manifest.json and verification-receipt.json
    by EXACT relative path (no other exclusion, incl. no __pycache__ allowance).
 3. Frozen input bindings: frozen/SHA256SUMS.frozen hashes match the actual
    frozen bytes; r320-chain and r326-original proposals.json are byte-identical.
 4. Retained primary bindings: inputs/2008.01164v2.html and -abs.html are
    byte-identical to the r320 frozen originals (7a05e419…, 5a9d72fb…).
 5. Work results re-validated: certified-bounds.json matches orbit-search.json
    aggregation and n!-2 counts; semantic-validation.json all_ok true.
Exit 0 iff all checks pass.
"""
import os, sys, json, hashlib

ROOT = os.path.dirname(os.path.abspath(__file__))
EXCLUDE = {"manifest.json", "verification-receipt.json"}
failures = []


def check(name, cond):
    print(("PASS " if cond else "FAIL ") + name, flush=True)
    if not cond:
        failures.append(name)


def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()


# 1+2: manifest bindings and exact payload enumeration
man = json.load(open(os.path.join(ROOT, 'manifest.json')))
listed = {e['path']: e for e in man['files']}
disk = set()
for root, dirs, files in os.walk(ROOT):
    for f in files:
        rel = os.path.relpath(os.path.join(root, f), ROOT)
        if rel not in EXCLUDE:
            disk.add(rel)
check("manifest_covers_disk_payload", disk == set(listed))
check("manifest_file_count", man['payload_count'] == len(listed))
bad = []
for p, e in listed.items():
    fp = os.path.join(ROOT, p)
    if not os.path.exists(fp):
        bad.append((p, 'missing'))
        continue
    b = open(fp, 'rb').read()
    if hashlib.sha256(b).hexdigest() != e['sha256'] or len(b) != e['size']:
        bad.append((p, 'hash_or_size'))
check("manifest_hash_size_bindings", not bad)

# 3: frozen bindings
frozen = {}
for line in open(os.path.join(ROOT, 'frozen', 'SHA256SUMS.frozen')):
    parts = line.split()
    if len(parts) == 2:  # hash lines only (stat appendix lines have >2 fields)
        frozen[parts[1]] = parts[0]
fbad = [n for n, h in frozen.items() if sha(os.path.join(ROOT, 'frozen', n)) != h]
check("frozen_input_bindings", not fbad)
check("r328_chain_equals_r326_original",
      frozen['input-A-r328-proposals.json'] == frozen['input-B-r326-proposals.json'])

# 4: retained primary byte-identity with r320 frozen originals
check("primary_body_byte_identical_to_r320",
      sha(os.path.join(ROOT, 'inputs', '2008.01164v2.html')) == '7a05e4198c96e0c0f8f85006daaea285ecd18277fa82c8c67b842378247d3770')
check("primary_abs_byte_identical_to_r320",
      sha(os.path.join(ROOT, 'inputs', '2008.01164-abs.html')) == '5a9d72fb13c245e648a4fd811f6d14069506c8117736b109cb2f4cdd99fbc3f4')

# 5: work results consistency
sv = json.load(open(os.path.join(ROOT, 'work', 'semantic-validation.json')))
check("semantic_validation_all_ok", sv['all_ok'] is True)
os_search = json.load(open(os.path.join(ROOT, 'work', 'orbit-search.json')))
bounds = json.load(open(os.path.join(ROOT, 'work', 'certified-bounds.json')))
agg = {}
for k, v in os_search.items():
    if 'chunk' in k:
        n = k.split('_n')[1].split('_')[0]
        name = k.split('_full')[0]
        key = (name, n)
        a = agg.setdefault(key, {'max': 0, 'all': True, 'count': 0})
        a['max'] = max(a['max'], v['max_hit'])
        a['all'] &= v['all_hit']
        a['count'] += v['count']
    else:
        name = k.rsplit('_full', 1)[0]
        n = k.rsplit('_n', 1)[1]
        agg[(name, n)] = {'max': v['max_hit'], 'all': v['all_hit'], 'count': v['count']}
import math
okb = True
for (name, n), v in agg.items():
    b = bounds[f"{name}_n{n}"]
    if not (b['max'] == v['max'] and b['all'] and v['all']
            and v['count'] == math.factorial(int(n)) - 2):
        okb = False
check("certified_bounds_consistent", okb and len(agg) == 16)

print("VERIFIER:", "ALL OK" if not failures else f"FAILURES {failures}")
sys.exit(0 if not failures else 1)
