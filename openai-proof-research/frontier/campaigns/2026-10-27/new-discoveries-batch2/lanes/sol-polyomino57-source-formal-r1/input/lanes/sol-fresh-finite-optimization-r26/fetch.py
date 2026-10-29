import pathlib,urllib.request,datetime,json,hashlib,re
L=pathlib.Path(__file__).resolve().parent
urls={
'oeis':'https://oeis.org/A395495',
'author-repo':'https://github.com/pexley-math/oeis-A395495',
'omega-live':'https://github.com/the-omega-institute/trureturing',
'openai-live':'https://github.com/openai/math',
'omega-polyomino':'https://raw.githubusercontent.com/the-omega-institute/trureturing/fb587b0e94c9169d5d1076c186dd766253eb5255/D5/S3/Combinatorics/Polyomino/LPolyominoSkippedSequence.lean',
'omega-dossier':'https://raw.githubusercontent.com/the-omega-institute/trureturing/fb587b0e94c9169d5d1076c186dd766253eb5255/Problems/condon-dugan-goldman-williams-2026-l-polyomino-skipped-sequence.md',
'author-companion':'https://raw.githubusercontent.com/pexley-math/oeis-A352029/main/README.md'}
log=[]
for name,url in urls.items():
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as r: data=r.read(6000000);rec['status']=r.status
  path=L/'sources'/f'{name}.txt';path.write_bytes(data);rec.update(path=str(path.relative_to(L)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  rec['currentOid']=list(set(re.findall(r'"currentOid":"([a-f0-9]{40})"',data.decode(errors='replace'))))
 except Exception as e:rec['error']=str(e)
 log.append(rec)
(L/'http-log.json').write_text(json.dumps(log,indent=2))
print(json.dumps(log,indent=2))
