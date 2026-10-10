#!/usr/bin/env python3
"""Freeze this review's read passages/observations. Does not touch any prior seal."""
import sys
sys.dont_write_bytecode=True
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i51_hard_moment_quantitative_stability_novelty'
E=R/'frontier/experiments/i51_hard_moment_quantitative_stability_novelty'
sha=lambda b:hashlib.sha256(b).hexdigest()
def save(name,data): (S/name).write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
specs={
 'centered-v2':[(1,150),(722,835),(922,1094),(1198,1498),(1808,1835)],
 'berman':[(128,163),(1258,1285),(1546,1620)],
 'bonnet':[(170,235),(1001,1065)],'cule':[(140,165),(270,338)],
 'figalli':[(50,73),(130,240)],'klartag':[(65,84),(1305,1360)],
 'bd':[(240,284),(450,1013),(1617,1900)],
 'bh':[(1,255),(500,838),(839,885)],
 'hug-schneider':[(1,274)],'fmp':[(70,200),(1464,1599)],
 'lu':[(109,152),(289,425),(475,532)],'xi':[(558,766),(805,943)],
 'vanhandel':[(713,857)],'klr':[(1,50),(208,242),(1870,1960)],
 'wang':[(230,252),(740,815)],'he-liu':[(188,204),(498,596)],
 'minkowski2026':[(1,310),(812,1000)],
 'mr':[(1,340),(1117,1435),(1670,1825),(2378,2390)],
 'ccm':[(460,682)],
}
rows=[]
def add(src,a,b,scope):
 p=S/src;raw=p.read_bytes();lines=raw.splitlines(keepends=True)
 if b is None:b=len(lines)
 assert 1<=a<=b<=len(lines),(src,a,b,len(lines))
 extract=b''.join(lines[a-1:b]);name=f'passages/{len(rows):03d}.txt'
 (S/name).parent.mkdir(exist_ok=True);(S/name).write_bytes(extract)
 rows.append(dict(source=src,source_sha256=sha(raw),first_line=a,last_line=b,extract=name,sha256=sha(extract),bytes=len(extract),scope=scope))
for name,ranges in specs.items():
 for a,b in ranges:add('primary/'+name+'.txt',a,b,'Actual selected statement/proof passage read; not a whole-paper audit')
for name in ['introduction','reduction','moment','identities','density','tensor','variance','measure']:
 matches=list((S/'frozen/frontier/sources/i49_hard_moment_quantitative_stability/pinned').rglob(name+'.tex'))
 assert len(matches)==1,(name,matches)
 add(str(matches[0].relative_to(S)),1,None,'Accepted pinned proof operations, full file read')
for f,ranges in {
 'frontier/iterations/i49-hard-moment-quantitative-stability.md':[(1,None)],
 'frontier/iterations/i46-quantitative-logarithmic-stability.md':[(1,None)],
 'frontier/reviews/i47-planar-logarithmic-stability-r2.md':[(1,None)],
 'frontier/reviews/i48-planar-logarithmic-stability-novelty.md':[(1,85)],
 'frontier/iterations/i44-logarithmic-equality-polytopes.md':[(355,491)],
 'frontier/reviews/i45-logarithmic-equality-r2.md':[(1,311)],
 'frontier/experiments/i49-parent-verification.json':[(1,None)],
 'AGENTS.md':[(1,None)],
}.items():
 for a,b in ranges:add('frozen/'+f,a,b,'Prior input actually read; historical statuses retain their scope')
save('read-passages.json',rows)
versions=[]
for p in sorted((S/'primary').glob('*')):
 if p.suffix not in ['.html','.txt']:continue
 lines=p.read_text().splitlines()
 evidence=[l for l in lines if ('arXiv:' in l and re.search(r'\d{4}\.\d+',l)) or ('Submitted on' in l) or ('Last revised' in l) or ('[v' in l and ('submission-history' in '\n'.join(lines) or p.suffix=='.html')) or 'arxiv.org/html/' in l]
 if evidence:versions.append(dict(file=str(p.relative_to(S)),sha256=sha(p.read_bytes()),version_lines=evidence))
save('versions.json',versions)
responses=json.loads((S/'responses.json').read_text())+json.loads((S/'extra-responses.json').read_text())
save('network-summary.json',dict(responses=len(responses),successes=sum(x['ok'] for x in responses),failures=sum(not x['ok'] for x in responses),pdfs=sum((S/x['file']).read_bytes().startswith(b'%PDF') for x in responses),scope='Fresh primary retrieval only; five saved web discovery responses are separate'))
save('execution-notes.json',[
 dict(action='Initial preparation',status='FAILED',error='json.decoder.JSONDecodeError: Expecting value: line 1 column 1 (char 0)',cause='Selected paths[13] instead of the named task JSON file; list element was a README',preserved='prepare-initial-failed.py',resolution='Owned prepare.py selects the exact iteration51 task path; successful run then froze the brief'),
 dict(action='Report title correction by apply_patch',status='FAILED_NO_CHANGE',error='Failed to find expected lines',cause='Expected escaped inline math delimiters, while the newly authored report had plain parentheses from JavaScript string escaping',resolution='Owned report corrected with exact text replacement and inline math delimiters normalized; no primary or predecessor file changed'),
 dict(action='I49 evidence replay',status='PASS_WITH_EXPLICIT_IN_MEMORY_ORDER_NORMALIZATION',record='i49-normalized-replay.json',scope='Only raw rg stdout comparison changed to sorted line multiset; author file and seal untouched'),
 dict(action='Original I49 parent history',status='MIXED_SEE_RECORD',record='frozen/frontier/experiments/i49-parent-verification.json',scope='Initial unmodified failure, later successful unmodified retry, direct replay, and normalized replay are distinct'),
])
run=subprocess.run([sys.executable,'-B',str(E/'check.py')],capture_output=True,check=True,cwd=R)
(E/'check-output.json').write_bytes(run.stdout)
print(json.dumps(dict(read_records=len(rows),version_records=len(versions),network=json.loads((S/'network-summary.json').read_text()))))
