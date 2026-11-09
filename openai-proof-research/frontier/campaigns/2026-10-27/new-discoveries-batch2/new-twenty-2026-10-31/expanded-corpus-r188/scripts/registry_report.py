import pathlib,json,re,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];rows=json.loads((D/'reservation.json').read_text())['rows'];terms=[str(r['mathdb_id']) for r in rows]+[r['source_url'].split('/')[-1] for r in rows]+['Nordh','signed shift','cordial','hypertree','Reitzner','Römer','Galashin','Pylyavskyy','Melo','Winter','pseudocircle','wall-crossing','Spiga','Nilakantan','Mazhar','Banica','Nechita','Dmitrishin','Tsuchiya','Monov','optical','Kneser']
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'terms':terms,'registries':{},'github_queries':[],'limitation':'Metadata and path screens only; no universal semantic proof-body clearance and no novelty claim.'}
for name in ['pool','omega','openai']:
 out['registries'][name]={'head':json.loads((D/f'sources/{name}-head.body').read_text())['sha'],'head_receipt':f'sources/{name}-head.receipt.json'}
hits=[]
for p in list((D/'sources').glob('pool-file-*.body'))+list((D/'sources').glob('pool-*.body')):
 if p.name in ['pool-head.body','pool-tree.body']:continue
 for n,line in enumerate(p.read_text().splitlines(),1):
  match=[t for t in terms if t.lower() in line.lower()]
  if match:hits.append({'file':str(p.relative_to(D)),'line':n,'terms':match,'text':line[:500]})
out['registries']['pool'].update(hits=hits,conclusion='No direct target match found in inspected project/candidate metadata; broad name/keyword hits do not imply matching statements.')
for name in ['D5','Problems']:
 p=D/f'sources/omega-{name}.body';x=json.loads(p.read_text());matches=[e['path'] for e in x['tree'] if any(t.lower() in e['path'].lower() for t in terms)]
 out['registries']['omega'][name]={'entries':len(x['tree']),'truncated':x['truncated'],'path_hits':matches,'receipt':str(p.with_suffix('.receipt.json').relative_to(D))}
p=D.parent/'fresh-corpus-r10/sources/registry-preprints.json'
if p.exists():
 b=p.read_bytes();x=json.loads(b);out['registries']['openai'].update(cached_preprints_path=str(p),cached_sha256=hashlib.sha256(b).hexdigest(),screen_hits=[t for t in terms if t.lower() in b.decode().lower()],note='HEAD unchanged from supplied baseline; cached path listing reused, proof bodies unread.')
for p in sorted((D/'sources').glob('github-search-*.receipt.json')):
 r=json.loads(p.read_text());body=p.with_name(p.name.replace('.receipt.json','.body'));x=json.loads(body.read_text()) if body.exists() else {};out['github_queries'].append({'receipt':str(p.relative_to(D)),'url':r['url'],'status':r.get('status'),'utc':r['utc'],'count':x.get('total_count'),'hits':[i['full_name'] for i in x.get('items',[])]})
(D/'outputs/registry-screen.json').write_text(json.dumps(out,indent=2));print('pool hits',len(hits),'github',len(out['github_queries']),'omega',[(k,len(v.get('path_hits',[]))) for k,v in out['registries']['omega'].items() if isinstance(v,dict)])
