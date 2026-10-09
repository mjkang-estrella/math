#!/usr/bin/env python3
"""Freeze this review's small inputs; reuse all author/corpus source bytes read-only."""
from pathlib import Path
import hashlib, json, datetime, urllib.request

R = Path(__file__).resolve().parents[3]
S = R/'frontier/sources/i30_einstein_metric_stability_r2'
A = R/'frontier/sources/i30_einstein_metric_stability'
sha = lambda b: hashlib.sha256(b).hexdigest()
def dump(p, obj):
    p.write_text(json.dumps(obj, indent=2, ensure_ascii=False)+'\n')
def row(p):
    b=p.read_bytes()
    return dict(path=str(p.relative_to(R)), bytes=len(b), sha256=sha(b))

small = ['AGENTS.md','frontier/TEN-FINDINGS.md','sources/upstream.json',
 'frontier/iterations/i30-einstein-metric-stability.md',
 'frontier/experiments/i30-parent-verification.json',
 'frontier/iterations/iteration27-geometric-analysis-discovery-task.json']
small += [str((A/p).relative_to(R)) for p in ['task-brief.txt','contracts.json',
 'input-manifest.json','source-manifest.json','artifact-seal.json',
 'literature/manifest.json','primary-versions.json']]
# The parent relocated this unsealed integration note during review.
small += ['frontier/sources/i30-parent-preliminary-review.md']
frozen=[]
for name in small:
    p=R/name; dest=S/'frozen'/name
    dest.parent.mkdir(parents=True,exist_ok=True); dest.write_bytes(p.read_bytes())
    frozen.append(dict(**row(p), frozen=str(dest.relative_to(R)), shared=name=='frontier/TEN-FINDINGS.md'))
dump(S/'input-manifest.json',dict(time=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=frozen))

paths=set()
for x in json.loads((A/'artifact-seal.json').read_text())['files']: paths.add(x['path'])
for x in json.loads((A/'source-manifest.json').read_text())['files']: paths.add(x['local'])
for x in json.loads((A/'input-manifest.json').read_text())['files']:
    if not x.get('shared'): paths.add(x['path'])
paths.update(['frontier/experiments/i30-parent-verification.json',str((A/'artifact-seal.json').relative_to(R))])
dump(S/'dependency-manifest.json',dict(policy='Read-only reuse; no corpus cache copy.',files=[row(R/p) for p in sorted(paths)]))

eg='frontier/sources/i27_geometric_analysis_discovery/pinned/preprints/An-L2-Einstein-Gap-for-Nonnegatively-Curved-Four-Manifolds-October-5-2026/build/source/main.tex'
e0='frontier/sources/i27_geometric_analysis_discovery/pinned/preprints/Zero-Plane-Rigidity-for-Einstein-Four-Manifolds-October-4-2026/build/sections/'
ep='frontier/sources/i27_geometric_analysis_discovery/pinned/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/build/sections/'
lit='frontier/sources/i30_einstein_metric_stability/literature/'
specs=[
 ('frontier/iterations/i30-einstein-metric-stability.md',1,None,'Full candidate, every mathematical step'),
 ('frontier/iterations/i27-geometric-analysis-discovery.md',1,None,'Full prior gap report; Screen A controls prior objections'),
 (eg,1,None,'Full EG; quantitative constants, smoothing, moving frame, energy, compactness'),
 (e0+'01-introduction.tex',1,None,'Exact zero-plane and nonnegative classification statements'),
 (e0+'08-classification.tex',1,None,'Boundary splitting and full classification interfaces'),
 (ep+'08-classification.tex',1,None,'Strict classification, normalization and global isometry'),
 (lit+'GV2015.txt',105,145,'Lichnerowicz convention and infinitesimal Einstein rigidity'),
 (lit+'GV2015.txt',730,825,'Actual slice proof; distinguish beta from pure divergence gauge'),
 (lit+'GV2015.txt',1275,1305,'Remark 2.15: pure divergence alternative'),
 (lit+'GV2015.txt',1510,1530,'TT Ricci linearization'),
 (lit+'GV2015.txt',2368,2595,'CP2 spectral normalization and full product spectral proof'),
 (lit+'1202.2912v1.txt',999,1050,'Exact local theorem hypotheses'),
 (lit+'1202.2912v1.txt',1165,1435,'Error smoothing and one-sided distance argument; Lemma 4.4 start'),
 (lit+'1202.2912v1.txt',1436,1815,'Complete missing-ball and curve-packing argument; Theorem 4.1'),
]
passages=[]
for i,(name,start,end,purpose) in enumerate(specs,1):
    p=R/name; b=p.read_bytes(); lines=b.splitlines(keepends=True); end=end or len(lines)
    frag=b''.join(lines[start-1:end]); out=S/'passages'/f'{i:02d}.txt'
    out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(frag)
    passages.append(dict(path=name,start=start,end=end,file_sha256=sha(b),sha256=sha(frag),retained=str(out.relative_to(R)),purpose=purpose))
dump(S/'read-passages.json',dict(scope='Only these ranges claimed read; source retention is not semantic reading.',passages=passages))

retrievals=[]
for ident in ['1105.4648v2','1202.2912v1']:
    url='https://arxiv.org/abs/'+ident
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I30-proof-review/1.0'}),timeout=30) as response:
            b=response.read(); final=response.url; status=response.status
        p=S/(ident+'-abs.html');p.write_bytes(b)
        retrievals.append(dict(**row(p),url=url,final_url=final,status=status,retrieved=datetime.datetime.now(datetime.timezone.utc).isoformat(),purpose='Version metadata only; retained author primary full texts control proof.'))
    except Exception as exc: retrievals.append(dict(url=url,error=str(exc)))
dump(S/'new-primary-manifest.json',dict(retrievals=retrievals))
print(json.dumps(dict(frozen_inputs=len(frozen),read_only_dependencies=len(paths),read_passages=len(passages),new_metadata_retrievals=len(retrievals))))
