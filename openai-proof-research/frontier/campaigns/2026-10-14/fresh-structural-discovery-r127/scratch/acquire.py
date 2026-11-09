from pathlib import Path
import json,urllib.request,hashlib,concurrent.futures,sys
root=Path(__file__).resolve().parents[1]; repo=root.parents[3]
tree=json.loads((repo/'sources/preprints-tree.json').read_text()); recpath=root/'packet/private/canonical.json'; records=json.loads(recpath.read_text()) if recpath.exists() else []
terms=sys.argv[1:]; rows=[x for x in tree['tree'] if x['type']=='blob' and x['path'].endswith(('.tex','.bib')) and any(w in x['path'] for w in terms) and '/figures/' not in x['path']]; have={r['canonical']['path'] for r in records}
def get(x):
 u='https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/'+x['path'];b=urllib.request.urlopen(u,timeout=45).read(); sha=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest();assert sha==x['sha'] and len(b)==x['size'];p=root/'packet/private/upstream'/x['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);return {'canonical':x,'url':u,'sha256':hashlib.sha256(b).hexdigest(),'local':str(p.relative_to(root/'packet'))}
with concurrent.futures.ThreadPoolExecutor(max_workers=6) as ex:
 for x in ex.map(get,[x for x in rows if x['path'] not in have]):records.append(x)
recpath.write_text(json.dumps(records,indent=2)+'\n');print('canonical records',len(records))
for x in rows:print(x['path'],x['size'])
