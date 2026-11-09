import json,pathlib,urllib.request,hashlib,datetime
L=pathlib.Path(__file__).resolve().parents[1]
for repo,label in [('openai/math','openai'),('the-omega-institute/trureturing','omega')]:
 h=json.loads((L/'sources'/f'{label}-head.json').read_text());sha=h['sha']; print(label,sha,flush=True)
 url=f'https://api.github.com/repos/{repo}/git/trees/{sha}'
 try:
  with urllib.request.urlopen(url,timeout=20) as f:b=f.read()
  (L/'sources'/f'{label}-root.json').write_bytes(b)
  root=json.loads(b)
  for ent in root['tree']:
   if ent['path'] in ('preprints','D5','Problems'):
    u=ent['url']+'?recursive=1'
    with urllib.request.urlopen(u,timeout=25) as f:body=f.read()
    name=f"{label}-{ent['path']}-tree.json";(L/'sources'/name).write_bytes(body)
    r={'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':200,'sha256':hashlib.sha256(body).hexdigest(),'file':'sources/'+name,'truncated':json.loads(body).get('truncated')}
    with (L/'outputs/http.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
    paths=[v['path'] for v in json.loads(body)['tree']];(L/'sources'/f"{label}-{ent['path']}-paths.txt").write_text('\n'.join(paths));print(name,len(paths),r['truncated'],flush=True)
 except Exception as e:print(type(e).__name__,str(e),flush=True)
