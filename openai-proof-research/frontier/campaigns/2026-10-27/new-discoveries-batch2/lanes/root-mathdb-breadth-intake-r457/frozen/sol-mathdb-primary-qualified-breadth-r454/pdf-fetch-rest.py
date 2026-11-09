import pathlib,json,hashlib,datetime,urllib.request,urllib.error,re,subprocess
L=pathlib.Path(__file__).resolve().parent;a=json.loads((L/'source-provenance.json').read_text())
for p in sorted((L/'sources').glob('*.html')):
 if p.with_suffix(".pdf").exists():continue
 m=re.search(r'name="citation_pdf_url" content="([^"]+)"',p.read_text());assert m,p
 url=m[1];row=dict(url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),version='published report; DOI and date in retained publisher HTML',article=p.stem)
 try:
  with urllib.request.urlopen(url,timeout=18) as r:b=r.read(12000000);row.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),path='sources/'+p.stem+'.pdf')
  (L/row['path']).write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(L/row['path']),str(p.with_suffix('.txt'))],check=True)
 except Exception as e:row.update(status=getattr(e,'code',None),error=str(e))
 a.append(row);(L/'source-provenance.json').write_text(json.dumps(a,indent=2)+'\n');print(p.stem,row.get('status'),row.get('error',''),flush=True)
 if row.get('status') in [403,429] or 'error' in row:break
