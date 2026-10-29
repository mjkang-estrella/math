import sys,json,hashlib,datetime,urllib.request,re,os,subprocess
from pathlib import Path
L=Path(__file__).resolve().parent; B=L.parents[1]; R=L.parents[5]
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def sha(b):return hashlib.sha256(b).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
(L/'sources').mkdir(exist_ok=True)
mode=sys.argv[1]
if mode=='history':
 old=L.parent/'sol-fresh-source-discovery-r138/history-receipt.json'; j=json.loads(old.read_bytes()); known={p:h for p,h,z in j['records']}; paths=set(known)
 roles={'summary.md','discovery.md','proof.md','review.md','decision.md'}
 skip={'.git','.lake','node_modules','__pycache__','extracted','copy','fresh','replay','history','inputs','evidence','build','vendor','dist','.venv','payload','private','context'}
 for root,ds,fs in os.walk(R):
  ds[:]=[d for d in ds if d not in skip and Path(root)/d!=L]
  for n in fs:
   if n.lower() in roles:paths.add(str((Path(root)/n).relative_to(R)))
 pat=re.compile(sys.argv[2],re.I); records=[]; hits=[]; changed=[]
 for p in sorted(paths):
  f=R/p
  if not f.exists():continue
  b=f.read_bytes();h=sha(b);records.append([p,h,len(b)])
  if known.get(p)!=h:changed.append(p)
  if pat.search(b.decode(errors='replace')):
   hits.append(p);(L/'sources'/('history-'+h+'.txt')).write_bytes(b)
 save('history-receipt.json',dict(utc=now(),baseline=str(old),baseline_sha256=sha(old.read_bytes()),records=records,changed=changed,pattern=pat.pattern,hits=hits,cutoff=None,scope='retained qualified original role paths plus changed/new originals; generated echoes skipped by role'))
 print('paths',len(records),'changed',len(changed),'hits',hits)
elif mode=='alias':
 j=json.loads((L/'history-receipt.json').read_bytes());pat=re.compile(sys.argv[2],re.I);hits=[]
 for p,h,z in j['records']:
  b=(R/p).read_bytes()
  if pat.search(b.decode(errors='replace')):
   hits.append(p);(L/'sources'/('history-'+sha(b)+'.txt')).write_bytes(b)
 rec=dict(utc=now(),pattern=pat.pattern,hits=hits,bodies=len(j['records']),cutoff=None)
 with (L/'alias-queries.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(rec)
elif mode=='fetch':
 for arg in sys.argv[2:]:
  name,url=arg.split('=',1);rec=dict(utc=now(),name=name,url=url)
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research-source-audit/1.0'}),timeout=30) as f:
    b=f.read(12000001)
    if len(b)>12000000:raise ValueError('12MB cap')
    (L/'sources'/name).write_bytes(b);rec.update(status=f.status,final_url=f.url,sha256=sha(b),bytes=len(b))
  except Exception as e:rec['error']=str(e)
  with (L/'http.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
  print(rec)
elif mode=='context':
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  b=(B/n).read_bytes();(L/('context-'+n)).write_bytes(b)
  if n.endswith('.json'):
   j=json.loads(b);print(n,[(a.get('number'),a.get('title')) for a in j.get('accepted',[])])
  else:
   print(b.decode()[:30000])
elif mode=='registry':
 out={}
 for name in ['omega-head.json','openai-head.json']:
  j=json.loads((L/'sources'/name).read_bytes());out[name]=dict(sha=j['sha'],commit_utc=j['commit']['committer']['date'],returned_files=len(j.get('files',[])))
 print(out);save('heads.json',out)
elif mode=='registry-screen':
 import gzip
 pat=re.compile(r'\bEntin\b|\bLandsberg\b|2310[.]04164|360245|Cilleruelo|PolynomialLCM|PolynomialLcm',re.I);out=[]
 for p in [L.parent/'root-edge-irregulator-final-freeze-r1/omega-tree.txt.gz',L.parent/'root-edge-irregulator-final-freeze-r1/openai-tree.txt.gz',L.parent/'sol-fresh-source-discovery-r138/sources/omega-compare.json']:
  b=gzip.decompress(p.read_bytes()) if p.suffix=='.gz' else p.read_bytes()
  lines=[s for s in b.decode().splitlines() if pat.search(s)]
  out.append(dict(path=str(p),sha256=sha(p.read_bytes()),hits=lines,limit='cached path/compare screen; no whole-current-body clearance'))
 save('registry-screen.json',out);print(json.dumps(out,indent=2))
elif mode=='finalize':
 j=json.loads((L/'sources/omega-fixed-delta.json').read_bytes());paths=[f['filename'] for f in j.get('files',[])]
 pat=re.compile(r'\bEntin\b|\bLandsberg\b|2310[.]04164|360245|Cilleruelo|PolynomialLCM',re.I)
 delta=dict(base='a19a578cd06b57a4ea4d287cb0df92f9085117ae',head='490f6bccbf445ab8e111a16b0b8670a5dd7c9a9c',total_commits=j['total_commits'],returned_commits=len(j['commits']),returned_paths=len(paths),paths=paths,matches=[p for p in paths if pat.search(p)],capped=len(paths)>=300,semantic_clearance=False,inherited_gap='aa026 to a19a exactly300 paths remains CAPPED')
 save('registry-delta.json',delta);print({k:v for k,v in delta.items() if k!='paths'})
 inherited=[]
 for rel in ['sol-fresh-source-discovery-r133/history-receipt.json','sol-fresh-source-discovery-r133/registry-delta-receipt.json','sol-fresh-source-discovery-r137/history-receipt.json','sol-fresh-source-discovery-r138/history-receipt.json','sol-fresh-source-discovery-r138/registry-delta-receipt.json','sol-fresh-source-discovery-r138/original-r111-r113-receipt.json']:
  p=L.parent/rel;inherited.append(dict(path=str(p),sha256=sha(p.read_bytes()),limit='inherited scope only; not current target body clearance'))
 guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
 ctx=[]
 for n in ['ledger.json','prior-campaign-context.json','NEXT.md']:
  p=L/('context-'+n);ctx.append(dict(source=str(B/n),retained=str(p),sha256=sha(p.read_bytes()),mutable=n=='NEXT.md'))
 prov=dict(finalized_utc=now(),outcome='zero nominees; full target unresolved',counts=dict(additional=9,total=39,next=40),write_scope=str(L),source='Entin–Landsberg Conjecture1.1, Acta Arithmetica217(2025)159–187; arxiv2310.04164v4',http=[json.loads(s) for s in (L/'http.jsonl').read_text().splitlines()],inherited=inherited,context=ctx,guard=dict(path=str(guard),sha256=sha(guard.read_bytes()),AS_bytes=536870912,group_RSS_bytes=536870912,CPU_seconds=210,wall_seconds=230,nominal_sample_ms=40,unchanged=True,sampling_limit='sampled process-group RSS/CPU does not certify continuous peaks; tool receipts for retrievals were not all redirected into files'),checks=json.loads((L/'checks.json').read_bytes()),registry=delta,remaining_gates=['full ordinary source resolution','target-specific current proof-body and classical screening','independent substantive/investment clearance before Lean or paper'],access_limits=['No403/429/challenge encountered in this lane','No worldwide priority claim','Cached path screens do not clear actual theorem bodies','Broad initial collision display clipped; exact target query uncapped','No exhaustive citer/original Hilbert/Leumi body audit'],searches=dict(utc_limit='performed during turn; no separate per-query UTC, not backdated',queries=['2025 algebra conjecture numerical semigroup polynomial','2024 number theory conjecture divisibility Fibonacci','2025 conjecture polynomial irreducible Integers','2024 open question finite groups probability','2025 conjecture gcd integers journal','Entin Landsberg least common multiple arxiv','2310.04164 proof conjecture','Entin Landsberg conjecture function fields proof2026','360245 Lean','least common multiple function fields conjecture counterexample','Hilbert irreducibility over function fields Bary Soroker Entin quantitative','site:github.com360245','site:github.com/trureturing function LCM']),git=False,children=False,browser_tabs=False,public_mutations=False,Lean=False,manuscript=False)
 save('provenance.json',prov)
 excluded={'finalmanifest.json','finalmanifest.sha256','manifest-verification.json','manifest-verification.log','finalize.log'}
 files=[]
 for p in sorted(L.rglob('*')):
  if p.is_file() and p.name not in excluded:files.append(dict(path=str(p.relative_to(L)),sha256=sha(p.read_bytes()),bytes=p.stat().st_size))
 save('finalmanifest.json',dict(utc=now(),files=files,exclusions=sorted(excluded),limit='manifest and verification receipts excluded to avoid recursive self hashing'))
 (L/'finalmanifest.sha256').write_text(''.join(f"{x['sha256']}  {x['path']}\n" for x in files))
 print('manifest entries',len(files))
