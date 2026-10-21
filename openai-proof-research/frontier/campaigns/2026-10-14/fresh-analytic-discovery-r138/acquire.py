from pathlib import Path
import urllib.request,json,hashlib,concurrent.futures
R=Path(__file__).resolve().parent;P=R.parents[3]
pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'
b=(P/'sources/preprints-tree.json').read_bytes();d=json.loads(b)
assert len(d['tree'])==13223 and hashlib.sha256(b).hexdigest()=='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b'
(R/'private/preprints-tree.json').write_bytes(b)
es=[e for e in d['tree'] if 'integer-degree-harmonic-dimension-comparison' in e['path'].lower() and e['type']=='blob' and e['path'].endswith(('.tex','.md'))]
def get(e):
 url=f'https://raw.githubusercontent.com/openai/math/{pin}/{e["path"]}'
 b=urllib.request.urlopen(url,timeout=40).read();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert len(b)==e['size'] and blob==e['sha'],e['path']
 local=Path('private/source')/e['path'];p=R/local;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
 return dict(canonical_path=e['path'],url=url,size=len(b),git_blob=blob,sha256=hashlib.sha256(b).hexdigest(),local_path=str(local),lines=len(b.splitlines()),read_extents=[])
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: rows=list(ex.map(get,es))
(R/'source-ledger.json').write_text(json.dumps(rows,indent=2)+'\n')
print('authenticated',len(rows),'source bodies')
for x in rows: print(x['local_path'].split('/')[-1],x['lines'])
