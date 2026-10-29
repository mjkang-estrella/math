import pathlib,hashlib,json,datetime,sys,shutil
L=pathlib.Path(__file__).resolve().parent; B=L.parent
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for s in iter(lambda:f.read(65536),b''):h.update(s)
 return h.hexdigest()
sets=[('candidate','root-renyi-threshold-review-freeze-r1','sol-fresh-source-discovery-r111'),('preliminary','root-renyi-preliminary-adoption-r1','sol-renyi-threshold-preliminary-review-r1')]
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sets':{}}
for label,freeze,original in sets:
 m=B/freeze/'review-freeze.json'; data=json.loads(m.read_text()); rows=[]
 for rel,expected in data.items():
  p=B/original/rel; got=digest(p); rows.append({'path':str(p),'bytes':p.stat().st_size,'expected':expected,'actual':got,'match':got==expected})
 out['sets'][label]={'manifest':str(m),'manifest_sha256':digest(m),'count':len(rows),'all_match':all(r['match'] for r in rows),'files':rows}
(L/(sys.argv[1]+'.json')).write_text(json.dumps(out,indent=2)+'\n')
if sys.argv[1]=='before':
 for original,rels in [('sol-fresh-source-discovery-r111',['PROOF.md','SUMMARY.md','sources/reverse.txt']),('sol-renyi-threshold-preliminary-review-r1',['review.md','search-notes.md'])]:
  for rel in rels:
   dst=L/'core'/original/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(B/original/rel,dst)
print(json.dumps({k:{'count':v['count'],'all_match':v['all_match']} for k,v in out['sets'].items()}))
assert all(v['all_match'] for v in out['sets'].values())
