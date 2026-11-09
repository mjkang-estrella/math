import json,pathlib,hashlib,urllib.request,concurrent.futures
base=pathlib.Path(__file__).resolve().parents[1]; root=base.parents[3]
tree=json.loads((root/'sources/preprints-tree.json').read_text()); assert len(tree['tree'])==13223 and tree['truncated'] is False
prefix='preprints/The-entropy-rate-dimension-formula-for-self-similar-measures-on-the-line-September-24-2026/'
entries=[x for x in tree['tree'] if x['path'].startswith(prefix) and x['path'].endswith(('.tex','.bib')) and '/sections/' in x['path']]
def fetch(x):
 url='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path']; b=urllib.request.urlopen(url,timeout=45).read(); g=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest(); assert g==x['sha']; out=base/'packet/private/upstream'/pathlib.Path(x['path']).name; out.write_bytes(b); return dict(path=x['path'],url=url,git_blob=g,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),local=str(out.relative_to(base/'packet')),tree_entry=x)
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as e: rows=list(e.map(fetch,entries))
(base/'packet/private/upstream/receipts.json').write_text(json.dumps(rows,indent=2)+'\n'); print([(r['local'],r['bytes']) for r in rows])
