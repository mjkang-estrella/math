import json,sys,hashlib,re,sqlite3,time
from pathlib import Path
from html.parser import HTMLParser
L=Path(__file__).resolve().parent
def out(n,v): (L/n).write_text(json.dumps(v,indent=2)+'\n')
class Text(HTMLParser):
 def __init__(self): super().__init__();self.x=[]
 def handle_data(self,d):
  if d.strip():self.x.append(d.strip())
if sys.argv[1]=='read':
 for name in ['ulam-v2','log-v1','log-history','ulam-history','ramsey-v2','ulam-origin-v2']:
  t=Text();t.feed((L/'sources'/f'{name}.html').read_text());(L/'sources'/f'{name}.txt').write_text('\n'.join(t.x)+'\n')
 for name in ['omega-head','openai-head']:
  j=json.loads((L/'sources'/f'{name}.json').read_text());print(name,j['sha'],j['commit']['committer']['date'])
 j=json.loads((L/'sources/omega-delta.json').read_text())
 p=re.compile('Yamamura|Cullinan|logarithm|Ulam|DiNasso|Di.Nasso|Pairwise|Jin|2401.14138|2410.01217',re.I)
 hits=[dict(path=f['filename'],patch=f.get('patch')) for f in j.get('files',[]) if p.search(f['filename']+' '+f.get('patch',''))]
 r=dict(status=j.get('status'),ahead_by=j.get('ahead_by'),total_commits=j.get('total_commits'),returned_commits=len(j.get('commits',[])),returned_files=len(j.get('files',[])),base=j.get('base_commit',{}).get('sha'),merge_base=j.get('merge_base_commit',{}).get('sha'),hits=hits,cap_warning=len(j.get('commits',[]))>=250 or len(j.get('files',[]))>=300,semantic_clearance=False)
 out('registry-delta-receipt.json',r);print(r)
elif sys.argv[1]=='hits':
 for line in (L/'refined-matches.jsonl').open():
  j=json.loads(line);print(j['path'],j['count']);print(j['excerpts'])
elif sys.argv[1]=='checks':
 lock=json.loads((L/'scientific-freeze.json').read_text());bad=[]
 for e in lock['files']:
  if hashlib.sha256((L/e['path']).read_bytes()).hexdigest()!=e['sha256']:bad.append(e['path'])
 assert not bad,bad
 # Literal distinct-concatenand recursion; short finite diagnostics only.
 levels={1:{'0','1'}};expected={1:2,2:2,3:4,4:8}
 samples=[]
 for n in range(2,15):
  counts={}
  for k in range(1,n):
   for a in levels[k]:
    for b in levels[n-k]:
     if a!=b:counts[a+b]=min(2,counts.get(a+b,0)+1)
  levels[n]={w for w,c in counts.items() if c==1}
  assert all(''.join('1' if c=='0' else '0' for c in w) in levels[n] and w[::-1] in levels[n] for w in levels[n])
  assert n not in expected or len(levels[n])==expected[n]
  samples.append({'n':n,'count':len(levels[n]),'parity_counts':[sum(int(w,2)%2==r for w in levels[n]) for r in range(2)]})
 assert len(levels[13])==1916 and len(levels[14])==3812
 out('check-results.json',dict(status='PASS',scientific_files=len(lock['files']),bad=bad,finite_recursion=samples,scope='Byte integrity and finite source-definition diagnostics only. No universal result or novelty inference.'))
 print('PASS',len(lock['files']),'source files; literal recursion through 14, no source conjecture proved')
elif sys.argv[1]=='seal':
 # Remove inherited, unused r127-only metadata command; no inherited claim is executed.
 p=L/'work.py';s=p.read_text();a=s.index("elif sys.argv[1]=='metadata':");b=s.index("elif sys.argv[1]=='manifest':",a);p.write_text(s[:a]+s[b:])
 hist=json.loads((L/'history-receipt.json').read_text());http=[json.loads(x) for x in (L/'http.jsonl').read_text().splitlines()]
 guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
 out('provenance.json',dict(lane=str(L),status='NO_ELIGIBLE_NOMINATION',credit=0,counts_as_read={'additional':9,'total':39,'next':40},source_http=http,guard={'path':str(guard),'sha256':hashlib.sha256(guard.read_bytes()).hexdigest(),'AS_bytes':536870912,'sampled_group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'nominal_ms':40,'BLAS_threads':1,'unchanged':True},history=hist,registry='registry-delta-receipt.json',solo=True,children=False,git=False,shared_edits=False,browser_tabs=False,external_mutations=False,lean_or_paper=False,primary_scope={'A39':'Conjecture1 all n>=1; journal proof bodies and arXiv v1 read; original Yamamura MR3976464 and original 2019 theorem not read.','A102':'Conjecture3 all fixed moduli and residues; current v2 Conjecture1.3, journal, source growth proof and earlier symmetry proof read.','A105':'dagger and literal final Q12; entire journal Sections2–3 read, final p7 visually inspected; later Ramsey companion selected proof bodies only.'},limits=['No source resolution or novelty PASS.','Initial combined context output, raw JSON HEAD display and one excerpt display truncated; retained bytes and bounded parsed reads control.','Initial unsharded scan terminated exit137 after210.66s at CPU limit, sampled peak47050752 bytes. Partial database/pathmap preserved as failed evidence, not coverage. Guard cap unchanged.','Sharded replacement has no global hit cutoff; per-body excerpts capped8, actual full representatives reopened for exact target searches.','Formats, generated roles, oversized and binary omissions are enumerated in shard receipts. Lexical/semantic gaps remain.','No whole r111–r113 exclusion; original scientific bodies are in eligible paths.','HEAD checked once each; delta 21commits18paths from fixed9a026 to2108, ancestry checked; no semantic absence inference.','Original 2019 logarithm theorem and MathSciNet review inaccessible/unread; exhaustive later-source search not claimed.','Scientific local copies frozen separately from mutable NEXT.','No403/429/challenge observed; no bypass, external messages or account action.']))
 # Inspect full original representatives again, independent of broad excerpts.
 db=sqlite3.connect(L/'history.sqlite');receipts=[]
 targets=[]
 for j in json.loads((L/'history-matches.json').read_text()):targets.append(j['path'])
 # r111-r113 original scientific reports are deliberately retained and individually recorded.
 retained=[]
 for h,p in db.execute('select h,path from bodies'):
  if re.search(r'/sol-fresh-source-discovery-r11[123]/(?:SUMMARY|discovery|progress|PROOF|review)[.]md$',p):retained.append([h,p])
 out('retained-r111-r113-science.json',retained)
 R=L.parents[5]
 for i,path in enumerate(targets):
  b=(R/path).read_bytes();h=hashlib.sha256(b).hexdigest();dest=f'sources/history-body-{i}.txt';(L/dest).write_bytes(b)
  exact=re.compile(rb'2401[.]14138|2410[.]01217|Yamamura|Cullinan|Gajek.Leonard|Ulam.words|Adutwum|17535327|17711561|Di.Nasso|Renling.Jin|pairwise.sum.theorem',re.I)
  hits=[m.start() for m in exact.finditer(b)]
  generated=bool(re.search(r'(?:tree|blob-paths|current-D5-paths|Golden|Blueprint|Problems)[.]json$',Path(path).name,re.I))
  target=bool(re.search(rb'2401[.]14138|2410[.]01217|truncated logarithmic polynomials|equidistribution conjecture for Ulam|From Schur.{0,30}Pairwise',b,re.I))
  receipts.append(dict(original=path,copy=dest,sha256=h,bytes=len(b),exact_reopen_matches=hits,generated_role=generated,target_specific=target,disposition='Generated registry navigation echo; excluded from scientific disposition.' if generated else ('Target catalogue record, requires original record classification.' if target else 'Surname/bibliography/truncated-logarithm coincidence, not the selected source question.')))
  if target and not generated:print('TARGET',path)
 out('original-reopen-receipts.json',receipts);print('sealed metadata; reopened',len(receipts),'full representatives; retained',len(retained),'r111-r113 originals')
