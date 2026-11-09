exec(compile(open(__file__.replace('extras.py','collect.py')).read().split('with concurrent.futures.ThreadPoolExecutor')[0],__file__,'exec'))
u={
'396838-pdf':'https://ems.press/content/serial-article-files/12864',
'stirling-journal':'https://www.math.tulane.edu/~vhm/papers_html/stirvaluation.pdf',
'stirling-2013':'https://www.maths.tcd.ie/EMIS/journals/JIS/VOL16/Mosteig/mosteig4.pdf',
'stirling-2009':'https://arxiv.org/pdf/0907.3412',
'knots-resolution':'https://arxiv.org/pdf/0805.2307',
'radical-survey':'https://u.cs.biu.ac.il/~plotkin/papers/survey-IJAC_rev.pdf',
'wide-2024':'https://arxiv.org/pdf/2408.04086',
'genus-proof':'https://arxiv.org/pdf/1606.04613',
'pool-projects':'https://raw.githubusercontent.com/leanprover-community/leanprover-community.github.io/master/data/projects.yml'
}
def run(pair):
 name,url=pair;rec={'label':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as r:b=r.read(15000000);rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));f=p/'sources'/name;f.write_bytes(b)
  if b.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(f),str(f)+'.txt'],timeout=20,check=True)
 except Exception as e:rec['error']=str(e)
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:rows=list(ex.map(run,u.items()))
(p/'extra-receipts.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
