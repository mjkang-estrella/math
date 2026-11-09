import pathlib,json,tarfile,gzip,hashlib,re
r=pathlib.Path(__file__).resolve().parents[1]; old=r.parent/'expanded-corpus-r204'
for p in sorted((r/'http').glob('*/receipt.json')):
 j=json.loads(p.read_text());u=j['url'];b=p.parent/'body'
 if j.get('status')!=200: continue
 if '/src/' in u:
  out=p.parent/'text';out.mkdir()
  if tarfile.is_tarfile(b):
   with tarfile.open(b) as t:
    for k,m in enumerate(t.getmembers()):
     if m.isfile() and m.name.endswith(('.tex','.bbl')) and m.size<2000000:
      data=t.extractfile(m).read();dest=out/(str(k)+'-'+pathlib.PurePosixPath(m.name).name);dest.write_bytes(data)
  else: (out/'main.tex').write_bytes(gzip.decompress(b.read_bytes()))
  for f in out.glob('*.tex'):
   ident=u.rsplit('/',1)[1][:-2];prev=old/'sources/tex'/ident/'main.tex'
   print('source',u,f.relative_to(r),'matches cache',prev.exists() and f.read_bytes()==prev.read_bytes())
 if '/git/trees/' in u:
  d=json.loads(b.read_text());print('tree truncated',d.get('truncated'))
  paths=[v['path'] for v in d['tree']];print('project config',[s for s in paths if 'projects.yml' in s]);print('candidate paths',[s for s in paths if s.startswith('candidates/')]); print('nim paths',[s for s in paths if re.search('nim|gurvich|naumova',s,re.I)])
 if '/search/repositories?' in u: print('GH search',json.loads(b.read_text())['total_count'])
 if '/search/?searchtype=author' in u:
  text=b.read_text(); print('author results',re.sub('<[^>]+>',' ',text)[:4000]);print('related snippets',[(m.start(),re.sub('<[^>]+>',' ',text[max(0,m.start()-250):m.end()+400])) for m in re.finditer('NIM|GM-rule|Screw|errat',text,re.I)])
