from work import *
ns={'a':'http://www.w3.org/2005/Atom'}
metadata={}
for p in S.glob('*.xml'):
 try:
  for e in E.fromstring(p.read_bytes()).findall('a:entry',ns):
   ident=e.findtext('a:id',default='',namespaces=ns).split('/abs/')[-1]
   metadata[ident]={'title':e.findtext('a:title',default='',namespaces=ns),'authors':[z.findtext('a:name',default='',namespaces=ns) for z in e.findall('a:author',ns)],'first':e.findtext('a:published',default='',namespaces=ns),'updated':e.findtext('a:updated',default='',namespaces=ns)}
 except E.ParseError:pass
binds=[json.loads(x) for x in (L/'bindings.jsonl').read_text().splitlines()]
out=[]
for b in binds:
 p=Path(b['original']);t=Path(b['text']);assert sha(p)==b['sha256'] and sha(t)==b['text_sha256']
 out.append(dict(b,metadata=metadata.get(p.stem),body_url='https://arxiv.org/pdf/'+p.stem))
(L/'primary-sources.json').write_text(json.dumps(out,indent=2))
# Administrative snapshots are parsed but never required to equal changing live administration.
for name in ['ledger.json','prior-campaign-context.json']:
 d=json.loads((L/'administrative'/name).read_text());print(name,list(d),d.get('accepted_count'))
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['final-manifest.json','final-verification.json']:
  files.append({'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':sha(p)})
(L/'final-manifest.json').write_text(json.dumps({'excludes':['final-manifest.json','final-verification.json'],'files':files},indent=2))
print('manifest entries',len(files))
