from pathlib import Path
import hashlib,json,re
L=Path(__file__).resolve().parent;B=L.parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
log=(L/'fresh-replay/logs/FullAudit.log').read_text()
assert sha(L/'fresh-replay/logs/FullAudit.log')==sha(L/'extracted/evidence/fresh-replay/logs/FullAudit.log')
rows=re.findall(r'^AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS \[([^\]]*)\]\nFLAGS unsafe=(\w+) partial=(\w+) axiom=(\w+)$',log,re.M|re.S)
assert len(rows)==31
(L/'declarations.json').write_text(json.dumps([{'origin':m,'name':n,'type':t,'axioms':a,'unsafe':u,'partial':p,'axiom':x} for m,n,t,a,u,p,x in rows],indent=2)+'\n')
out={'intervals':[],'body_count':0,'hits':[],'context':{}}
pat=re.compile(r'factorial|transversal|dissociat|subset.?product|Aivazidis|Loukaki|jgth-2024-0030',re.I)
R=B/'sol-renyi-registry-gap-closure-r3';old=None;commits=set()
for row in json.loads((R/'intervals.json').read_text()):
 path=Path(row['response']);path=path if path.is_absolute() else R/path
 d=json.loads(path.read_text());h=sha(path)
 assert h==row['sha256'];assert old is None or row['base']==old
 assert d['behind_by']==0 and len(d['files'])<300
 old=row['end'];commits.update(c['sha'] for c in d['commits'])
 out['intervals'].append({'path':str(path),'sha256':h,'base':row['base'],'head':old,'files':len(d['files'])})
 for f in d['files']:
  txt=f.get('patch','')
  if pat.search(f['filename']+'\n'+txt):out['hits'].append({'path':f['filename'],'excerpt':txt[:2400]})
seen=set()
for row in json.loads((R/'bodies.json').read_text()):
 if row.get('status')!='ok':continue
 p=R/row['source'];b=p.read_bytes()
 assert hashlib.sha256(b).hexdigest()==row['read']['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==row['actual_git_blob']
 if sha(p) in seen:continue
 seen.add(sha(p));out['body_count']+=1
 txt=b.decode(errors='replace')
 if p.suffix=='.json':
  def strings(x):
   if isinstance(x,str):yield x
   elif isinstance(x,list):
    for v in x:yield from strings(v)
   elif isinstance(x,dict):
    for v in x.values():yield from strings(v)
  txt='\n'.join(strings(json.loads(txt)))
 for m in list(pat.finditer(txt))[:5]:out['hits'].append({'body':str(p),'excerpt':txt[max(0,m.start()-100):m.end()+250]})
out['unique_commits']=len(commits)
out['later_cached_deltas']=[]
for p in [B/'sol-supertoken-preliminary-review-r1/omega-new-delta.json',B/'sol-factorial-product-prior-clearance-r2/fresh-delta.json']:
 d=json.loads(p.read_text());assert len(d['files'])<300
 out['later_cached_deltas'].append({'path':str(p),'sha256':sha(p),'files':len(d['files']),'commits':d['total_commits'],'missing':[f['filename'] for f in d['files'] if 'patch' not in f],'matches':[{'path':f['filename'],'excerpt':f.get('patch','')[:1200]} for f in d['files'] if pat.search(f['filename']+'\n'+f.get('patch',''))]})
for n in ['NEXT.md','ledger.json','AGENTS.md','prior-campaign-context.json']:
 p=B.parent/n;out['context'][str(p)]={'sha256':sha(p),'bytes':p.stat().st_size}
(L/'inherited-screen.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'intervals':len(out['intervals']),'unique_commits':len(commits),'unique_bodies':len(seen),'bounded_hits':len(out['hits'])}))
