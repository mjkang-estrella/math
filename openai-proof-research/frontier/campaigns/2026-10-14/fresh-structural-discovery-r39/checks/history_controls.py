#!/usr/bin/env python3
"""Finite infrastructure controls; no mathematical or novelty verdict."""
import hashlib,json,subprocess,sys,tempfile
from pathlib import Path
p=Path(__file__).resolve().parent.parent
j=json.loads((p/'history-index.json').read_text());ad=json.loads((p/'history-adjudications.json').read_text())
checks=[]
def record(name,ok):
    checks.append({'name':name,'pass':bool(ok)})
    if not ok:raise AssertionError(name)
reg={'129':['frontier/campaigns/2026-10-14/fresh-structural-discovery-r31/screen-129.md'],'324':['frontier/iterations/i88-nonlinear-banach-discovery.md','frontier/campaigns/2026-10-14/fresh-analytic-discovery-r22/checkpoint.md'],'188':['frontier/campaigns/2026-10-14/fresh-structural-discovery-r29/screen-188.md'],'150':['frontier/iterations/i52-ergodic-dynamical-discovery.md']}
for f,paths in reg.items():
    hits={x['path'] for x in j['families'][f]['authored_matches']}
    for name in paths:record(f+' -> '+name,name in hits and any(e['path']==name for e in ad[f]['evidence']))
record('no private or copied source-body evidence',not any(set(Path(x['path']).parts)&{'private','inputs','context','snapshots','preprints'} for x in j['artifacts']))
record('metadata is reference-only',all(x['class']=='metadata-reference' for x in j['artifacts'] if x['path'].endswith('.json')))
record('explicit unmapped complete-tree directories',len(j['uncatalogued_preprint_directories'])==30)
record('reference-only matches do not receive automatic developed status',all(x['path'].endswith('.json') for f in j['families'].values() for x in f['reference_matches']))
r=json.loads((p/'history-replay-result.json').read_text());record('full saved-domain byte replay',r['byte_identical'] and r['sha256']==hashlib.sha256((p/'history-index.json').read_bytes()).hexdigest())
# Deliberately changed first saved input must fail before any corpus scan.
with tempfile.TemporaryDirectory(prefix='.history-control-',dir=p) as d:
    root=Path(d);first=j['artifacts'][0];target=root/first['path'];target.parent.mkdir(parents=True);target.write_bytes(b'changed test input\n')
    q=subprocess.run([sys.executable,'-B',str(p/'build_history_index.py'),'--root',str(root),'--replay-index',str(p/'history-index.json'),'--output',str(root/'out.json')],capture_output=True,text=True)
    record('saved input drift rejected',q.returncode!=0 and 'history input drift:' in q.stderr and not (root/'out.json').exists())
print(json.dumps({'status':'PASS','controls':checks,'limits':'Only bounded search/provenance controls; absence is never clearance'},indent=2))
