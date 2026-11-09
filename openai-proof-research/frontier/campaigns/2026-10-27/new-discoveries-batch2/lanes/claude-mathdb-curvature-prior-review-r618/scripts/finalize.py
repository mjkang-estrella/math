"""Run verify.py logic plus bounded in-memory negative tests; write final-receipt.json only.
Usage (lane dir): python3 -I -B scripts/finalize.py"""
import copy, datetime, hashlib, importlib.util, json, os, subprocess, sys

spec = importlib.util.spec_from_file_location('lane_verify', os.path.abspath('verify.py'))
V = importlib.util.module_from_spec(spec); spec.loader.exec_module(V)

proc = subprocess.run([sys.executable, '-I', '-B', 'verify.py', '.'], capture_output=True, text=True)
files, links = V.load_tree('.')
files.pop('final-receipt.json', None)
man = json.loads(files['manifest.json'])
base = V.verify_tree(files, man, links)
target = next(e['path'] for e in man['files'] if e['path'] == 'review.md')


def case(name, fs, mf, lk=()):
    errs = V.verify_tree(fs, mf, lk)
    return {'case': name, 'rejected': bool(errs), 'errors': errs[:3]}

neg = []
f1 = dict(files); b = bytearray(f1[target]); b[0] ^= 1; f1[target] = bytes(b)
neg.append(case('byte_flip_same_size', f1, man))
f2 = dict(files); f2[target] = files[target] + b'\n'
neg.append(case('size_change_append', f2, man))
f3 = dict(files); f3['runs/extra.txt'] = b'x'
neg.append(case('extra_file', f3, man))
f4 = dict(files); del f4[target]
neg.append(case('missing_file', f4, man))
m5 = copy.deepcopy(man); m5['files'][0]['sha256'] = '0' * 64
neg.append(case('manifest_hash_edit', files, m5))
m6 = copy.deepcopy(man); m6['files'][0]['size'] += 1
neg.append(case('manifest_size_edit', files, m6))
m7 = copy.deepcopy(man); m7['files'].append({'path': '../x', 'size': 0, 'sha256': '0' * 64})
neg.append(case('path_traversal_entry', files, m7))
m8 = copy.deepcopy(man); m8['files'].append(copy.deepcopy(man['files'][0]))
neg.append(case('duplicate_entry', files, m8))
neg.append(case('symlink_present', files, man, ['runs/link']))
m9 = copy.deepcopy(man); m9['excluded_exact_paths'] = ['manifest.json']
neg.append(case('excluded_list_altered', files, m9))

mb = open('manifest.json', 'rb').read()
receipt = {
 'utc': datetime.datetime.now(datetime.timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ'),
 'lane': 'claude-mathdb-curvature-prior-review-r618',
 'manifest': {'size': len(mb), 'sha256': hashlib.sha256(mb).hexdigest(), 'entries': len(man['files'])},
 'verify_py': {'exit': proc.returncode, 'stdout': json.loads(proc.stdout) if proc.stdout.strip() else None, 'stderr': proc.stderr},
 'in_memory_baseline_errors': base,
 'negative_tests': neg,
 'all_negatives_rejected': all(n['rejected'] for n in neg),
 'scope': 'Integrity PASS only; not a mathematical, prior-art or novelty PASS',
}
json.dump(receipt, open('final-receipt.json', 'w'), indent=1)
ok = proc.returncode == 0 and not base and receipt['all_negatives_rejected']
print(json.dumps({'ok': ok, 'verify_exit': proc.returncode, 'negatives': len(neg)}))
sys.exit(0 if ok else 1)
