from pathlib import Path
import urllib.request,json,hashlib,datetime,re
P=Path(__file__).resolve().parent
meta=json.loads((P/'provenance.json').read_text());records=meta['retrievals']
def get(n,u):
 r={'file':n,'url':u,'accessed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=35) as f:b=f.read()
  (P/'sources'/n).write_bytes(b);r.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest());d=json.loads(b) if n.endswith('.json') else b
 except Exception as e:r['error']=str(e);d=None
 records.append(r);(P/'provenance.json').write_text(json.dumps(meta,indent=2));return d
for label,repo,dirs in [('omega','the-omega-institute/trureturing',['Problems','D5','Blueprint']),('openai','openai/math',['preprints']),('count','suvrit/count-ex-machina',[])]:
 h=json.loads((P/'sources'/f'{label}-head.json').read_text()) if label!='count' else get('count-head.json',f'https://api.github.com/repos/{repo}/commits/HEAD')
 if not h:continue
 sha=h['sha'];print(label,sha,flush=True)
 root=get(label+'-root.json',f'https://api.github.com/repos/{repo}/git/trees/{sha}'+('' if dirs else '?recursive=1'))
 for dn in dirs:
  ent=next(x for x in root['tree'] if x['path']==dn)
  t=get(label+'-'+dn+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{ent["sha"]}?recursive=1')
  assert t and not t['truncated']
  hits=[x for x in t['tree'] if re.search(r'tsallis|renyi|wu-yu-guo|alzer.berg|bernstein.boundary|2609.28707',x['path'],re.I)]
  (P/'sources'/f'{label}-{dn}-hits.json').write_text(json.dumps(hits,indent=2));print(dn,len(t['tree']),len(hits),flush=True)
  for x in hits:
   if dn=='Problems' or (dn=='preprints' and x['path'].endswith('.tex')):print(x['path'],flush=True)
 if label=='openai':get('current-CONTENTS.md',f'https://raw.githubusercontent.com/{repo}/{sha}/CONTENTS.md')
 if label=='count':get('count-registry.json',f'https://raw.githubusercontent.com/{repo}/{sha}/registry.json')
get('alzer-source.html','https://arxiv.org/html/2609.28707v1')
get('alzer-abs.html','https://arxiv.org/abs/2609.28707')
