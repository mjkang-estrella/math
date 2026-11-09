import json,hashlib,urllib.request,pathlib,concurrent.futures,datetime
R=pathlib.Path(__file__).resolve().parent; root=R.parents[3]; pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
T=json.loads((root/'sources/preprints-tree.json').read_text()); assert len(T['tree'])==13223 and T['truncated']==False
families={'177':'Bounded-degree-coboundary-expanders','169':'Elementary-Positivity-of-Chromatic','113':'Entropy-and-Face-Dimension'}
entries=[(f,e) for f,k in families.items() for e in T['tree'] if k in e['path'] and e['path'].endswith(('.tex','.bib')) and '/figures/' not in e['path'] and '/appendices/' not in e['path']]
def get(fe):
 f,e=fe; path=e['path']; url=f'https://raw.githubusercontent.com/openai/math/{pin}/{path}'; b=urllib.request.urlopen(url,timeout=60).read(); blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(); assert blob==e['sha']
 dest=R/'packet/private/upstream'/f/path.split('/build/')[1];dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(b)
 return dict(family=f,path=path,raw_url=url,git_blob=blob,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),local=str(dest.relative_to(R/'packet')),acquisition='fresh pinned HTTP',utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex: receipts=list(ex.map(get,entries))
(R/'packet/private/upstream-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
(R/'packet/private/selected-tree.json').write_text(json.dumps([e for f,e in entries],indent=2)+'\n')
(R/'packet/private/tree-receipt.json').write_text(json.dumps(dict(path='sources/preprints-tree.json',sha256=hashlib.sha256((root/'sources/preprints-tree.json').read_bytes()).hexdigest(),entries=len(T['tree']),truncated=T['truncated'],pin=pin),indent=2)+'\n')
print([(f,sum(r['bytes'] for r in receipts if r['family']==f)) for f in families])
