import urllib.request,json,hashlib,datetime,pathlib
P=pathlib.Path(__file__).resolve().parent
meta=json.loads((P/'provenance.json').read_text()) if (P/'provenance.json').exists() else {'retrievals':[]}
def get(n,u):
 r={'file':n,'url':u,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(u,timeout=35) as f:b=f.read()
  (P/'sources'/n).write_bytes(b);r.update(sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));d=json.loads(b) if n.endswith('.json') else b
 except Exception as e:r['error']=str(e);d=None
 meta['retrievals'].append(r);(P/'provenance.json').write_text(json.dumps(meta,indent=2));return d
if __name__=='__main__':
 for label,repo,dirs in [('omega','the-omega-institute/trureturing',['Problems','D5','Blueprint']),('openai','openai/math',['preprints']),('count','suvrit/count-ex-machina',[])]:
  h=get(label+'-head.json',f'https://api.github.com/repos/{repo}/commits/HEAD')
  if not h:continue
  print(label,h['sha'],h['commit']['committer']['date'],flush=True)
  root=get(label+'-root.json',f'https://api.github.com/repos/{repo}/git/trees/{h["sha"]}'+('' if dirs else '?recursive=1'))
  for dn in dirs:
   ent=next(x for x in root['tree'] if x['path']==dn);t=get(label+'-'+dn+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{ent["sha"]}?recursive=1');assert not t['truncated']
  if label=='count': get('count-registry.json',f'https://raw.githubusercontent.com/{repo}/{h["sha"]}/registry.json')
 for id in ['2410.23009v1','2102.07083v1','1907.09644v1']:
  get(id+'.html','https://arxiv.org/html/'+id)
