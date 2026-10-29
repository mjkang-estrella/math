from pathlib import Path
import json,hashlib,datetime
b=Path(__file__).parent;batch=b.parent.parent
now=datetime.datetime.now(datetime.timezone.utc).isoformat()
q=['ambrus','gargyan','laplacepolya','laplace-polya','eulerian','sinc','lesieur','baxter','hoggatt','filaseta','banerjee']
regs=[]
for name in ['omega-D5.json','omega-Problems.json']:
 d=json.loads((b/'sources'/name).read_text());assert not d['truncated']
 regs.append(dict(file='sources/'+name,sha=d['sha'],truncated=d['truncated'],entries=len(d['tree']),hits=[x['path'] for x in d['tree'] if any(t in x['path'].lower() for t in q)]))
inherit=[]
r32=batch/'lanes/sol-fresh-source-discovery-r32/sources'
for name in ['cached-inherited-aim-full-current-tree.json','cached-inherited-count-count-full-tree.json','cached-inherited-openai-openai-preprints-tree.json']:
 p=r32/name;d=json.loads(p.read_text());seq=d if isinstance(d,list) else d['tree']
 inherit.append(dict(path=str(p.resolve()),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),entries=len(seq),hits=[x if isinstance(x,str) else x['path'] for x in seq if any(t in str(x).lower() for t in q)]))
heads={name:json.loads((b/'sources'/fn).read_text())['sha'] for name,fn in [('omega-dev','omega-head.json'),('omega-main','omega-main-current.json'),('openai','openai-head.json'),('aim','aim-head.json'),('count','count-current.json')]}
delta=json.loads((b/'sources/omega-delta.json').read_text())
reg=dict(utc=now,heads=heads,queries=q,scopes=regs,inherited_scopes=inherit,compare=dict(total_commits=delta['total_commits'],returned_commits=len(delta['commits']),returned_files=len(delta['files']),file_cap_hit=len(delta['files'])>=300,usable_for_absence=False),limits=['Whole dev not retrieved','Current complete named subtrees only; filename screen is not proof of absence','Actual nearest bodies read; no external Lean replay','Wrong initial count-head.json is teorth/analysis and is NOT Count registry; corrected count-current.json used','Five pinned registry heads unchanged except dev versus r37'],novelty_pass=False)
(b/'registry-screen.json').write_text(json.dumps(reg,indent=2)+'\n')
reads=[('ambrus.pdf','internal pp16–18 all text; pp17–18 rendered and visually inspected; pp19–20 reference23'),('baxter.pdf','pp2 definition1.1; pp3–4 theorem scope; pp8–10 recurrence3.4/eventual theorem discussion; pp10–11 Conjectures4.1–4.3'),('integers.pdf','pp1–5 Question1,Conjecture1,Theorems1–3; remaining pages not claimed read'),('sun.pdf','pp1–3 definitions and introduction; no whole paper read'),('baxter-mao.pdf','pp17–18 Theorem5.1/proof setup; pp29–31 Theorem6.1 and proof'),('hoggatt.pdf','pp16–17 Eq6.1,Theorem6.1,Proposition6.2 and proof'),('omega-sinc.lean','header,definitions and theorem-name scope, not whole proof audit'),('omega-semi-baxter.lean','header/result and proof setup, not whole proof audit'),('baxter-mathdb.json','complete post body; empty solutions not treated as novelty'),('sun-mathdb.json','posted solution body beginning and all-order obstruction attribution; no replay of complete posted proof')]
prov=dict(schema_version=1,lane=str(b.resolve()),utc=now,status='NO_FULL_RESULT',selected_target='Fang–Zhang–Zhao arXiv2505.05873v1 Conjecture4.2',ordinary_proof='INCOMPLETE',published_source='HOLD HTTP403',count_authority=False,external_mutations=False,children=False,git=False,lean_started=False,read_ranges=[dict(file='sources/'+n,range=r) for n,r in reads],download_only=['companion.pdf (Ambrus2024)','ambrus-home.html (384bytes,not bibliography evidence)','gargyan-home.html (not used to certify publication completeness)'],http_log='http.json',registry='registry-screen.json',checks=['check.py','probe.py','probe-high.py'],limits={'AS_bytes':512*1024**2,'CPU_seconds_each':35,'alarm_seconds_each':45,'shell_timeout_seconds_each':50,'BLAS_threads':1},model='gpt-6.1-sol',reasoning='high',speed='default',source_scope='Public HTTP/search only; no browser/account/post/upload/contact',inherited_documents=[])
for name in ['AGENTS.md','ledger.json','prior-campaign-context.json']:
 p=batch/name;prov['inherited_documents'].append(dict(path=str(p.resolve()),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reading='AGENTS full; JSON parsed fully, selected entries examined; initial combined display truncated' if name!='AGENTS.md' else 'full'))
for p in [Path('openai-proof-research/AGENTS.md'),batch/'lanes/sol-fresh-source-discovery-r37/SUMMARY.md']:
 prov['inherited_documents'].append(dict(path=str(p.resolve()),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),reading='full'))
prov['exclusion_screen']='All previous lane SUMMARY.md searched for Ambrus/Gargyan/Laplace-Polya/Baxter/Hoggatt/Filaseta/Banerjee; only unrelated real-polarization Ambrus mention. User exclusions preserved; elliptic Bernoulli not revisited.'
(b/'provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
(b/'search-log.json').write_text(json.dumps(dict(utc=now,provider='web search tool; exact source bytes independently fetched with HTTP',queries=['conjecture log-convex 2025 polynomials sequence','conjecture irreducible 2024 Bernoulli polynomials','conjecture completely monotonic 2025 open problem','Ambrus Gargyan Laplace Polya log convex conjecture even sequence solution','Ambrus log-convexity Eulerian proof','normalized Eulerian maxima proof','2412.12835 log convex solution','Baxter numbers moment Stieltjes','Baxter infinitely log-convex proof','Banerjee Kundu Conjecture Filaseta 2026','Analytic properties arising from the Baxter numbers proof conjecture','Baxter log-convexity 2026 infinite','Lesieur Nicolas Eulerian pdf 379 399'],limits=['Bounded public search only; no MathSciNet/zbMATH audit','No claim of worldwide novelty','Do not treat secondary catalogue summaries as theorem bodies']),indent=2)+'\n')
manifest=[]
for p in sorted(b.rglob('*')):
 if p.is_file() and p.name!='manifest.json':manifest.append(dict(path=str(p.relative_to(b)),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(b/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(heads);print('manifest',len(manifest),'files')
