from pathlib import Path
import json,hashlib,datetime,tarfile,re,sys
L=Path(__file__).resolve().parent;B=L.parent.parent;R=L.parents[5]
def sha(b):return hashlib.sha256(b).hexdigest()
if sys.argv[1]=='context':
 out=[]
 for p in [R/'AGENTS.md',B/'AGENTS.md',B/'ledger.json',B/'prior-campaign-context.json',B/'NEXT.md',R/'sources/upstream.json',R/'sources/CONTENTS.md',R/'sources/preprints-tree.json']:
  b=p.read_bytes();out.append(dict(path=str(p),sha256=sha(b),bytes=len(b),role='mutable coordination' if p.name=='NEXT.md' else 'as-read context'))
  if p.suffix=='.json':
   j=json.loads(b)
   if isinstance(j,dict):print(p.name,'keys',list(j))
   if p.name=='ledger.json':print([(a['number'],a['title']) for a in j['accepted']])
   if p.name=='prior-campaign-context.json':
    for k,v in j.items():
     if isinstance(v,list):
      print(k,[{kk:vv for kk,vv in x.items() if kk in ('number','title','status','source_target')} for x in v if isinstance(x,dict)])
 (L/'context-receipts.json').write_text(json.dumps(out,indent=2))
elif sys.argv[1]=='classical':
 with tarfile.open(L/'sources/classical-source.tar') as t:
  for m in t.getmembers():
   if m.isfile() and m.name.endswith('.tex'):
    assert m.size<1000000
    b=t.extractfile(m).read();(L/'sources'/('classical-'+Path(m.name).name)).write_bytes(b);print(m.name,len(b))
elif sys.argv[1]=='reopen':
 j=json.loads((L/'history-receipt.json').read_bytes());out=[]
 for d in sorted({(R/x['path']).parent for x in j['hits']}):
  for p in sorted(d.iterdir()):
   if p.is_file() and p.name.lower() in ('summary.md','discovery.md','proof.md','review.md','decision.md'):
    b=p.read_bytes();out.append(dict(path=str(p),bytes=len(b),sha256=sha(b)));print(p,len(b))
 (L/'original-reopen-receipts.json').write_text(json.dumps(out,indent=2))
elif sys.argv[1]=='registry':
 j=json.loads((L/'sources/omega-fixed.json').read_bytes())
 r={k:j[k] for k in ['status','ahead_by','behind_by','total_commits']}
 r.update(base='aa026efa802f4361758b827d6b68231ac353948f',head='a19a578cd06b57a4ea4d287cb0df92f9085117ae',merge_base=j['merge_base_commit']['sha'],commits_returned=len(j['commits']),files_returned=len(j['files']),files_cap_ok=len(j['files'])<300,commit_cap_ok=len(j['commits'])==j['total_commits'],relevant_patch_hits=[],semantic_clearance=False,openai='unchanged 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a')
 p=re.compile('2180639[78]|Achour|degree.spread|wild.number|2610.22142',re.I)
 for f in j['files']:
  if p.search(f['filename']+'\n'+f.get('patch','')):r['relevant_patch_hits'].append(f['filename'])
 r['commit_summaries']=[dict(sha=c['sha'],utc=c['commit']['committer']['date'],message=c['commit']['message']) for c in j['commits']]
 r['retained_receipts']=[dict(path=str(L.parent/f'sol-fresh-source-discovery-r{n}/registry-delta-receipt.json'),sha256=sha((L.parent/f'sol-fresh-source-discovery-r{n}/registry-delta-receipt.json').read_bytes())) for n in (133,135,137) if (L.parent/f'sol-fresh-source-discovery-r{n}/registry-delta-receipt.json').exists()]
 (L/'registry-delta-receipt.json').write_text(json.dumps(r,indent=2));print({k:v for k,v in r.items() if k not in ('commit_summaries','retained_receipts')})
