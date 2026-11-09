"""Freeze scientific inputs (copies + hashes) and snapshot administrative files.
Usage: freeze.py <batch_dir> <lane_dir> <phase>   phase in {freeze, verify}"""
import hashlib, json, shutil, sys, os, datetime
B, L, phase = sys.argv[1], sys.argv[2], sys.argv[3]
D = 'lanes/sol-fresh-source-discovery-r215'
SCI = [D+'/SUMMARY.md', D+'/discovery.md', D+'/scientific-freeze.json', D+'/progress.md',
       D+'/frozen/projection.pdf', D+'/frozen/closest.pdf', D+'/frozen/projection-abs.html',
       D+'/frozen/closest-abs.html', D+'/checks.py', D+'/http.jsonl', D+'/provenance.json']
ADM = ['AGENTS.md', 'NEXT.md', 'ledger.json', 'prior-campaign-context.json',
       '../../../../AGENTS.md']
def h(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
if phase == 'freeze':
    rec = {'utc': now, 'scientific': [], 'administrative_snapshot_only': []}
    for rel in SCI:
        src = os.path.join(B, rel); dst = os.path.join(L, 'inputs', rel.replace(D + '/', 'r215/'))
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        before = h(src); shutil.copy2(src, dst); after = h(src); c = h(dst)
        assert before == after == c, rel
        rec['scientific'].append({'original': os.path.join('new-discoveries-batch2', rel), 'copy': os.path.relpath(dst, L), 'sha256': c, 'bytes': os.path.getsize(dst)})
    for rel in ADM:
        src = os.path.normpath(os.path.join(B, rel)); name = 'ancestor-AGENTS.md' if rel.startswith('..') else rel
        dst = os.path.join(L, 'administrative', name); os.makedirs(os.path.dirname(dst), exist_ok=True)
        shutil.copy2(src, dst)
        rec['administrative_snapshot_only'].append({'original': rel, 'copy': os.path.relpath(dst, L), 'sha256_at_snapshot': h(dst), 'note': 'mutable; snapshot only, not a scientific binding'})
    json.dump(rec, open(os.path.join(L, 'scientific-freeze.json'), 'w'), indent=1)
    print(json.dumps({'frozen': len(rec['scientific']), 'admin': len(rec['administrative_snapshot_only'])}))
else:
    rec = json.load(open(os.path.join(L, 'scientific-freeze.json')))
    out = {'utc': now, 'checks': []}
    for e in rec['scientific']:
        o = os.path.join(B, e['original'].replace('new-discoveries-batch2/', '', 1)); c = os.path.join(L, e['copy'])
        out['checks'].append({'copy': e['copy'], 'original_ok': h(o) == e['sha256'], 'copy_ok': h(c) == e['sha256']})
    for e in rec['administrative_snapshot_only']:
        out['checks'].append({'copy': e['copy'], 'snapshot_ok': h(os.path.join(L, e['copy'])) == e['sha256_at_snapshot']})
    out['all_ok'] = all(all(v for k, v in x.items() if k.endswith('_ok')) for x in out['checks'])
    print(json.dumps(out, indent=1))
