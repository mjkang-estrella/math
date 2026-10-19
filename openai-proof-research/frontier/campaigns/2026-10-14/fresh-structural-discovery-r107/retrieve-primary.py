# Original acquisition code; third-party bodies are private.
import pathlib, urllib.request, hashlib, json, subprocess
BASE=pathlib.Path(__file__).resolve().parent
urls={
 'degree-bounded-directed-network-design':'https://viswa.engin.umich.edu/wp-content/uploads/sites/169/2014/08/deg-bnd-siam.pdf',
 'atsp-asadpour':'https://www.cs.cmu.edu/~anupamg/papers/atsp-full.pdf',
 'minimum-crossing-polymatroid':'https://d-nb.info/125776778X/34',
}
records=[]
for key,url in urls.items():
 rec={'key':key,'url':url}
 try:
  data=urllib.request.urlopen(url,timeout=45).read()
  if not data.startswith(b'%PDF'): raise ValueError('not a PDF')
  path=BASE/'private'/'primary'/(key+'.pdf');path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
  out=path.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(path),str(out)],check=True)
  rec.update(success=True,local=str(path.relative_to(BASE)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),text_local=str(out.relative_to(BASE)),text_sha256=hashlib.sha256(out.read_bytes()).hexdigest())
 except Exception as ex:rec.update(success=False,error=str(ex))
 records.append(rec)
(BASE/'primary-receipts.json').write_text(json.dumps(records,indent=2)+'\n')
print(json.dumps(records,indent=2))
