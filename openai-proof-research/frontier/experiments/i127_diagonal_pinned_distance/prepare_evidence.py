"""One-time evidence preparation. Does not seal. Never called by the verifier."""
from pathlib import Path
import json,hashlib,re
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i127_diagonal_pinned_distance'; E=ROOT/'frontier/experiments/i127_diagonal_pinned_distance'
assert not (S/'seal.json').exists()
def rel(p):return str(p.relative_to(ROOT))
def sha(b):return hashlib.sha256(b).hexdigest()
def put(p,x):p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
def data(p):return json.loads(p.read_text())
# Exact originals, including every decoded field; no selected-field substitute.
task=data(S/'snapshots/frontier/iterations/iteration124-fractal-incidence-discovery-task.json')
assert sha((S/'snapshots/frontier/iterations/iteration124-fractal-incidence-discovery-task.json').read_bytes())=='bd1ed58fb0adf6d63d0b36b67a5092f78f1d2063cf19317dfadad70ee8c6f240'
assert task==data(S/'original-i124-decoded.json') and task['brief']==(S/'original-i124-brief.txt').read_text()
t127=data(S/'original-i127-task.json');assert t127['brief']==(S/'original-i127-brief.txt').read_text()
markers=['--- ORIGINAL DIRECT I124 BRIEF ---','--- ORIGINAL I124 REPORT ---','--- FINALIZED PARENT RESPONSE ---']
parts=[]
for i,m in enumerate(markers):
 t=t127['brief'].split(m,1)[1]
 if i+1<len(markers):t=t.split(markers[i+1],1)[0]
 name=['supplied-original-direct-i124-brief.txt','supplied-original-i124-report.txt','supplied-finalized-i124-parent-response.txt'][i]
 (S/name).write_text(t);parts.append(name)
assert (S/parts[1]).read_text().strip()==(S/'snapshots/frontier/iterations/i124-fractal-incidence-discovery.md').read_text().strip()
assert data(S/parts[2])==data(S/'snapshots/frontier/experiments/i124-parent-verification.json')
put(S/'input-freeze.json',{'all_decoded_fields':True,'task127':rel(S/'original-i127-task.json'),'brief127':rel(S/'original-i127-brief.txt'),'markers':markers,'parts':parts,'recursive_tasks':[{'path':rel(p),'sha256':sha(p.read_bytes())} for p in [S/'snapshots/frontier/iterations/iteration124-fractal-incidence-discovery-task.json',S/'original-i121-task.json',S/'original-i118-task.json']],'frozen_parent':rel(S/'snapshots/frontier/experiments/i124-parent-verification.json')})
# Retroactive bindings for displays made before read_support was installed.
m=data(S/'read-manifest.json')
def add(p,start,end,note=None):
 b=p.read_bytes();ls=b.decode().splitlines();v={'local':rel(p),'file_sha256':sha(b),'start':start,'end':min(end,len(ls)),'line_count':len(ls),'convention':'splitlines','passage_sha256':sha('\n'.join(ls[start-1:min(end,len(ls))]).encode())}
 if note:v['note']=note
 if v not in m['passages']:m['passages'].append(v)
for name,ranges in [('original-i124-brief.txt',[(1,95),(96,504)]),('original-i121-brief.txt',[(1,269),(270,632)]),('original-i118-brief.txt',[(1,275),(80,103),(276,456),(457,730),(731,1089)])]:
 for a,b in ranges:add(S/name,a,b,'Read in bounded commands before read_support; initial truncations separately logged and reread.')
for name in ['original-i124-decoded.json','original-i121-task.json','original-i118-task.json']:
 obj=data(S/name);put(S/(name.replace('.json','-other-fields.json')),{k:v for k,v in obj.items() if k!='brief'})
for name in ['AGENTS.md','README.md','sources/upstream.json']:
 add(S/'snapshots'/name,1,len((S/'snapshots'/name).read_text().splitlines()),'Full opening read; README reread after compacted context.')
add(S/'snapshots/frontier/README.md',24,24,'Current status line read by rg, not full historical ledger.')
# A failed whole-ledger display is not represented as a complete read.
for p in m['passages']:
 if p['local'].endswith('snapshots/frontier/TEN-FINDINGS.md') and p['start']==1 and p['end']==260:p['complete_display']=False;p['note']='Truncated display attempt; only visible opening/status and concluding sections counted. Not full semantic reading.'
put(S/'read-manifest.json',m)
# Flat direct bindings, not recursive verifier calls; old seals cover their owned evidence.
paths={p['local'] for p in m['passages'] if not p['local'].startswith(rel(S)+'/')}
paths|={'AGENTS.md','sources/upstream.json','sources/CONTENTS.md','frontier/iterations/iteration124-fractal-incidence-discovery-task.json','frontier/iterations/i124-fractal-incidence-discovery.md','frontier/experiments/i124-parent-verification.json','frontier/experiments/i124_fractal_incidence_discovery/extract_html.py','frontier/sources/i112_inverse_boundary_discovery/search-domain.json','frontier/sources/i88_nonlinear_banach_discovery/search-domain.json'}
# No active I125/I126 outputs and no live ledger as an immutable reference.
for p in paths:assert not re.search(r'i12[56]|iteration12[56]',p)
put(S/'immutable-references.json',[{'path':p,'sha256':sha((ROOT/p).read_bytes())} for p in sorted(paths)])
put(S/'html-bindings.json',[{'html':rel(p),'html_sha256':sha(p.read_bytes()),'text':rel(p.with_suffix('.txt')),'text_sha256':sha(p.with_suffix('.txt').read_bytes()),'extractor':'frontier/experiments/i124_fractal_incidence_discovery/extract_html.py','convention':'HTMLParser math alttext; omit script/style/math data; collapse whitespace per nonempty splitline; LF joined with final LF'} for p in sorted((S/'literature').glob('*.html'))])
# One flat corpus traversal for new exact expression. Inherited expressions are replayed together by verify.py.
expression=r'(?i)(pinned.{0,32}distance|diagonal.{0,32}pin|ball[- ]inflation|Mizohata|two[- ]depth)'
rx=re.compile(expression);hits=[]
domain=data(ROOT/'frontier/sources/i112_inverse_boundary_discovery/search-domain.json')
for x in domain:
 b=(ROOT/x['local']).read_bytes();assert sha(b)==x['sha256']
 for i,line in enumerate(b.decode('utf-8',errors='replace').splitlines(),1):
  mm=list(rx.finditer(line))
  if mm:hits.append({'path':x['path'],'local':x['local'],'splitlines_line':i,'text':line,'spans':[list(z.span()) for z in mm]})
put(S/'lexical-search.json',{'patterns':{'diagonal_pinned':expression},'results':{'diagonal_pinned':hits},'scope':'Exact full-domain lexical membership, spans and occurrence multiset, not semantic coverage.'})
put(S/'failure-log.json',{'inherited_failures':'All original failure logs and failed parent receipts are retained under their unchanged inherited seals; no prior failure removed.','new':[{'operation':'Initial combined task/ledger reads','result':'Tool-output truncation','handling':'Mandatory recursive briefs reread completely in bounded chunks; I118 lines 80-103 explicitly repeated. Whole historical ledger not claimed read.'},{'operation':'Liu 1-240 combined with web output','result':'Outer display truncation','handling':'Opening 1-81 reread; remaining relied-on proof through ending read in bounded chunks.'},{'operation':'Combined I02/R2/I36 output','result':'Output truncation','handling':'I02 complete visible; R2 70-81 and I36 57-85 repeated.'},{'operation':'TEN-FINDINGS 1-260','result':'Output truncation','handling':'Marked incomplete display; current acceptance/status and I124/I127 entries separately read.'}],'retrieval_failures':[],'limits':'No selected PDF reextraction; no claim finite diagnostics certify universal analysis.'})
print(json.dumps({'new_lexical_lines':len(hits),'direct_references':len(paths),'read_records':len(m['passages'])}))
