"""Integrity verifier for lane claude-mathdb-banzhaf-source-prior-review-r494.

Checks (exits non-zero on any mismatch):
  1. manifest.json lists EXACTLY every lane file except manifest.json and verification-receipt.txt,
     each with matching sha256 and size;
  2. every flat input binding in bindings.json matches the actual bytes at its batch path, and at
     its original r480 lane path where one is given;
  3. every retained fetched payload matches its fetch-log hash/size, and non-retained ones are absent;
  4. self-test: in-memory corruptions of a manifest entry, of a binding, and an extra unlisted file
     must each be rejected.
Integrity PASS is not a mathematics or novelty PASS.  Usage: python3 -I -B verify.py
"""
import hashlib
import json
import os
import sys

LANE = os.path.dirname(os.path.abspath(__file__))
BATCH = os.path.dirname(os.path.dirname(LANE))
EXCLUDED = {'manifest.json', 'verification-receipt.txt'}


def h(p):
    d = open(p, 'rb').read()
    return hashlib.sha256(d).hexdigest(), len(d)


def lane_files():
    out = set()
    for r, ds, fs in os.walk(LANE):
        for f in fs:
            out.add(os.path.relpath(os.path.join(r, f), LANE))
    return out


def check_manifest(man, actual):
    errs = []
    listed = {e['path']: e for e in man['files']}
    if set(man.get('excluded_exact_paths', [])) != EXCLUDED:
        errs.append('exclusion set differs')
    for p in sorted(actual - EXCLUDED - set(listed)):
        errs.append('unlisted file ' + p)
    for p in sorted(set(listed) - actual):
        errs.append('listed but missing ' + p)
    for p in sorted(set(listed) & EXCLUDED):
        errs.append('excluded path listed ' + p)
    for p, e in listed.items():
        if p in actual and p not in EXCLUDED:
            if h(os.path.join(LANE, p)) != (e['sha256'], e['size']):
                errs.append('hash/size mismatch ' + p)
    return errs


def check_bindings(b):
    errs = []
    for e in b['inputs']:
        for key in ('path_from_batch', 'original_path_from_batch'):
            if key in e:
                p = os.path.join(BATCH, e[key])
                if not os.path.isfile(p):
                    errs.append('binding missing ' + e[key])
                elif h(p) != (e['sha256'], e['size']):
                    errs.append('binding mismatch ' + e[key])
    for e in b['fetched']:
        p = os.path.join(LANE, e['lane_path'])
        if e['retained']:
            if not os.path.isfile(p) or h(p) != (e['sha256'], e['size']):
                errs.append('fetched mismatch ' + e['lane_path'])
        elif os.path.exists(p):
            errs.append('non-retained fetched payload present ' + e['lane_path'])
    if b.get('mathdb_requests') != 0 or b.get('upstream_verifiers_executed') != 0:
        errs.append('policy counters nonzero')
    return errs


def main():
    man = json.load(open(os.path.join(LANE, 'manifest.json')))
    b = json.load(open(os.path.join(LANE, 'bindings.json')))
    actual = lane_files()
    errs = check_manifest(man, actual) + check_bindings(b)
    # self-tests: each corruption must be detected
    st = {}
    bad = json.loads(json.dumps(man)); bad['files'][0]['sha256'] = '0' * 64
    st['manifest_hash_corruption_rejected'] = bool(check_manifest(bad, actual))
    st['extra_unlisted_file_rejected'] = bool(check_manifest(man, actual | {'planted.py'}))
    bad = json.loads(json.dumps(b)); bad['inputs'][0]['size'] += 1
    st['binding_corruption_rejected'] = bool(check_bindings(bad))
    bad = json.loads(json.dumps(b)); bad['fetched'][0]['sha256'] = 'f' * 64
    st['fetched_corruption_rejected'] = bool(check_bindings(bad))
    if not all(st.values()):
        errs.append('self-test failed ' + json.dumps(st))
    print(json.dumps({'lane': os.path.basename(LANE), 'manifest_files': len(man['files']),
                      'lane_files_excluding_exclusions': len(actual - EXCLUDED),
                      'input_bindings': len(b['inputs']), 'fetched_entries': len(b['fetched']),
                      'selftests': st, 'errors': errs, 'integrity': 'PASS' if not errs else 'FAIL',
                      'note': 'integrity only; not a mathematics or novelty PASS'}, indent=1))
    sys.exit(1 if errs else 0)


if __name__ == '__main__':
    main()
