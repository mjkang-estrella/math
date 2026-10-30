from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent;B=L.parents[1];R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
def rec(p):
 b=p.read_bytes();return dict(path=str(p),sha256=sha(b),bytes=len(b))
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
assert sha(guard.read_bytes())=='825ee0d48177cd12354cdbf36fd36b61f0503ff3241356a7bf638ee0bc49fa45'
inherited=[]
for r in ['sol-fresh-source-discovery-r157/provenance.json','sol-fresh-source-discovery-r159/provenance.json','sol-fresh-source-discovery-r159/registry-screen.json','sol-fresh-source-discovery-r159/history-qualification.json']:
 inherited.append(rec(L.parent/r))
old=json.loads((L.parent/'sol-fresh-source-discovery-r159/provenance.json').read_bytes())
checks=[]
for n in ['omega-head.json','openai-head.json']:
 p=L/'sources'/n;h=sha(p.read_bytes());target=next(x for x in old['http'] if x['name']==n);assert h==target['sha256'];checks.append(dict(name=n,sha256=h,r159_equal=True))
http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
save('provenance.json',dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),lane=str(L),status='ZERO_NOMINEES',credit=0,baseline_counts=dict(additional=9,total=39,next=40),governing=[rec(R/'AGENTS.md'),rec(B/'AGENTS.md')]+[rec(L/('context-'+n)) for n in ['ledger.json','prior-campaign-context.json','NEXT.md']],inherited=inherited,current_registry_response_hash_checks=checks,http=http,search_queries=['graph conjecture 2026 irregular domination partition','combinatorial conjecture 2026 unimodality graph polynomial','Achour saturation conjecture proof','Degree–Independent-Domination conjecture counterexample','graphical Stirling Yaqubi planar unimodality','minimum maximal matching independent domination maximum degree','Achour 21801900','smallest maximal matchings Tavakoli Doslic pdf'],search_limits='Bounded public web search; not archived search result bodies; no worldwide absence claim',guard=dict(**rec(guard),AS_bytes=536870912,group_RSS_bytes=536870912,CPU_seconds=210,wall_seconds=230,nominal_sampling_ms=40,limits='Sampled RSS can miss short peaks; /proc visibility limits retained; caps never raised'),failures=[dict(kind='MemoryError',command='first checks.py with unbounded cache and k2..7',exit=1,sampled_peak_group_rss=296865792,wall_seconds=4.568390541011468,correction='20000-state cache, explicit clear, reduced k2..5'),dict(kind='absent guessed history-refresh.py',exit=1),dict(kind='initial rg inventory before guard initialization',disclosed=True)],registry_limits=['Two inherited 300-path caps remain','No complete current-head semantic sweep','No current worldwide absence clearance'],primary_science=['sources/source.tar.gz','sources/paper.tex','sources/author-paper.tex','sources/stirling-source.html','sources/stirling.html','sources/cubic.pdf','sources/regular.pdf'],no_completion_claim=True,no_lean_or_manuscript=True))
# Verification output and the two manifests are intentionally not recursively hashed.
exclude={'finalmanifest.json','scientific-freeze.json','manifest-verification.json','verify.log'}
files=sorted(p for p in L.rglob('*') if p.is_file() and p.name not in exclude)
science=[p for p in files if p.name not in {'context-NEXT.md','context-ledger.json','context-prior-campaign-context.json'} and p.suffix!='.log']
save('scientific-freeze.json',dict(entries={str(p.relative_to(L)):sha(p.read_bytes()) for p in science},status='UNRESOLVED / public exclusion, no completion'))
save('finalmanifest.json',dict(entries={str(p.relative_to(L)):dict(sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in files}))
print('frozen',len(files),'payload paths;',len(science),'scientific paths')
