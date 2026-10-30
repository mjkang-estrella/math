from pathlib import Path
import json,hashlib,datetime,sys,urllib.request,urllib.error,re,subprocess
L=Path(__file__).resolve().parent; B=L.parent.parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
def dump(n,x): (L/n).write_text(json.dumps(x,indent=2)+'\n')
def init():
 for n in ['administrative','assigned','changed','sources','frozen','failures','receipts']: (L/n).mkdir(exist_ok=True)
 bindings=[]
 files=['root-r209-handback/DECISION.md','sol-fresh-source-discovery-r209/SUMMARY.md','sol-fresh-source-discovery-r209/discovery.md']+[f'root-r{n}-handback/DECISION.md' for n in [206,207,208]]
 for f in files:
  p=L.parent/f;q=L/'assigned'/f.replace('/','--');q.write_bytes(p.read_bytes());bindings.append(dict(original=str(p),copy=str(q),sha256=H(p)));assert H(q)==H(p)
 for n in ['ledger.json','prior-campaign-context.json','AGENTS.md','NEXT.md']:
  p=B/n
  if p.exists():(L/'administrative'/n).write_bytes(p.read_bytes())
 p=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/AGENTS.md');(L/'administrative/ancestor-AGENTS.md').write_bytes(p.read_bytes())
 g=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py';q=L/'guard-copy.py';q.write_bytes(g.read_bytes());bindings.append(dict(original=str(g),copy=str(q),sha256=H(g)))
 dump('bindings.json',bindings)
 for fn in ['qualified-original-index.json','alias-refresh.json']:
  old=json.loads((L.parent/'sol-fresh-source-discovery-r209'/fn).read_text());rows=old['records'];seen={r['original'] for r in rows}
  if fn.startswith('qualified'):
   for p in L.parent.glob('*/*'):
    if p.is_file() and p.name.lower() in ['summary.md','discovery.md','decision.md','review.md','proof.md'] and p.parent!=L and str(p) not in seen:
     rows.append(dict(original=str(p),sha256=None,snapshot_reference=None))
  changed=[]
  for i,r in enumerate(rows):
   p=Path(r['original']);previous=r['sha256'];ref=r.get('snapshot_reference')
   if ref: assert H(Path(ref))==previous,ref
   if p.exists():
    h=H(p);r.update(previous=previous,sha256=h,changed=h!=previous)
    if h!=previous:
     q=L/'changed'/f'{fn[:5]}-{i}-{p.parent.name}-{p.name}';q.write_bytes(p.read_bytes());assert H(q)==h;r['snapshot_reference']=str(q);changed.append(r['original'])
   else:r['missing_live_original']=True
  dump(fn,dict(utc=now(),records=rows,changed=changed))
 dump('workflow-failures.json',{'deviation':'Initial pwd/rg/head inventory ran without helper_guard before reading guard. Subsequent helper/retrieval/hash/edit commands guarded; native bounded instruction reads and apply_patch allowed. Initial assigned historical reports read before freeze; frozen byte copies now bound. No original scientific PDF body read before freeze.'})
 print('refresh',[(n,len(json.loads((L/n).read_text())['records']),len(json.loads((L/n).read_text())['changed'])) for n in ['qualified-original-index.json','alias-refresh.json']])
def fetch(url,name):
 r=dict(utc=now(),url=url,name=name)
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=35) as q:
   data=q.read(12000001);r.update(status=q.status,final_url=q.url,headers=dict(q.headers))
  assert len(data)<=12000000
  for n in ['sources','frozen']:(L/n/name).write_bytes(data)
  r.update(sha256=H(L/'sources'/name),bytes=len(data));assert H(L/'frozen'/name)==r['sha256']
 except Exception as e:
  r['error']=repr(e)
  if isinstance(e,urllib.error.HTTPError):
   data=e.read(200000);(L/'failures'/(name+'.body')).write_bytes(data);r['failure_sha256']=H(L/'failures'/(name+'.body'))
 with (L/'http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r))
def screen(terms,name):
 out=[]
 for fn in ['qualified-original-index.json','alias-refresh.json']:
  for r in json.loads((L/fn).read_text())['records']:
   p=Path(r['snapshot_reference']);assert H(p)==r['sha256'];s=p.read_text(errors='replace').lower()
   hits=[t for t in terms if t.lower() in s]
   if hits:out.append(dict(index=fn,original=r['original'],snapshot_reference=str(p),sha256=r['sha256'],hits=hits))
 dump(name,dict(utc=now(),terms=terms,hits=out));print(json.dumps(out)[:20000])
if __name__=='__main__':
 if sys.argv[1]=='init':init()
 elif sys.argv[1]=='fetch':fetch(*sys.argv[2:])
 elif sys.argv[1]=='screen':screen(sys.argv[3:],sys.argv[2])
 elif sys.argv[1]=='extract':
  name=sys.argv[2];q=subprocess.run(['pdftotext','-layout',str(L/'frozen'/(name+'.pdf')),'-'],capture_output=True);(L/(name+'.txt')).write_bytes(q.stdout);(L/'receipts'/(name+'.extract.stderr')).write_bytes(q.stderr);assert q.returncode==0
