import pathlib,json,hashlib,datetime,re
D=pathlib.Path(__file__).resolve().parents[1];ids=list(json.loads((D/'reservation.json').read_text())['ids']);sha=lambda b:hashlib.sha256(b).hexdigest();rec={}
for name in ['openai','omega']:
 p=D/f'sources/{name}-head.json';o=json.loads(p.read_text());matches=[]
 for f in o.get('files',[]):
  for i in ids:
   if re.search(r'(?<!\d)'+str(i)+r'(?!\d)',f.get('filename','')+' '+f.get('patch','')):matches.append(dict(id=i,path=f['filename']))
 rec[name]=dict(sha=o['sha'],commit_utc=o['commit']['committer']['date'],receipt=f'sources/{name}-head.json.receipt.json',head_response_sha256=sha(p.read_bytes()),changed_files=len(o.get('files',[])),matches=matches,limitation='HEAD commit response/changed-file screen only; not current full tree or semantic proof clearance. No other live registry route accessed.')
# Bind complete cached tree scopes but do not infer latest semantic clearance.
refs=[]
for p in [D.parent/'xor-magic-parent-final-r1/registries/omega-D5.body',D.parent/'xor-magic-parent-final-r1/registries/omega-Problems.body',D.parent/'fresh-corpus-r10/sources/registry-preprints.json']:
 if p.exists():
  data=p.read_bytes();o=json.loads(data);refs.append(dict(path=str(p),sha256=sha(data),id_path_hits=[i for i in ids if re.search(r'(?<!\d)'+str(i)+r'(?!\d)','\n'.join(z.get('path','') for z in o.get('tree',[])))],limitation='Cached path scope; content at newly observed HEAD not completely authenticated; no semantic proof clearance.'))
rec['cached_scopes']=refs;(D/'outputs/registry-screen.json').write_text(json.dumps(rec,indent=2))
# Record all required inputs, family exclusions and provenance references read-only.
inputs=[D/'TASK.txt',D/'reservation.json',D.parents[5]/'AGENTS.md',D.parent/'AGENTS.md',D.parent.parent/'AGENTS.md',D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']
(D/'outputs/input-bindings.json').write_text(json.dumps([dict(path=str(p),sha256=sha(p.read_bytes()),bytes=p.stat().st_size) for p in inputs if p.exists()],indent=2))
print(json.dumps(rec,indent=2))
