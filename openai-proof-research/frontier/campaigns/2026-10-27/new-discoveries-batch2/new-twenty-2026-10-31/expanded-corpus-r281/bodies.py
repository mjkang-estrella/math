exec((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('rows=json.loads')[0])
import re,subprocess
rec=json.loads((p/'receipts.json').read_text()); jobs=[]; histories={}
for r in rec:
 if '/abs/' not in r['url'] or r.get('status')!=200:continue
 s=(p/r['file']).read_text(); aid=r['url'].split('/abs/')[1]; vs=sorted(set(map(int,re.findall(r'\[v(\d+)\]',s))))
 histories[aid]={'versions':vs,'journal':re.findall(r'<td class="tablecell jref">(.*?)</td>',s,re.S),'doi':re.findall(r'https://doi.org/[^"< ]+',s)}
 for v in vs:jobs.append('https://arxiv.org/pdf/'+aid+'v'+str(v))
jobs+=['https://arxiv.org/pdf/0905.4822','https://arxiv.org/pdf/0908.2988','https://arxiv.org/pdf/1803.00730','https://web.mit.edu/yufeiz/www/papers/mstd_density.pdf','https://arxiv.org/pdf/1806.03426','https://arxiv.org/pdf/0712.0663','https://people.csail.mit.edu/schulz/papers/Rolling.pdf','https://escholarship.org/content/qt00c6r759/qt00c6r759.pdf','https://sites.lsa.umich.edu/hderksen/wp-content/uploads/sites/614/2018/05/A.I.a.33.pdf']
(p/'version-history.json').write_text(json.dumps(histories,indent=2)+'\n')
exec((p/'fetch.py').read_text().split('def fetch(url):')[1].split('with concurrent.futures')[0].join(['def fetch(url):','']))
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex: receipts=list(ex.map(fetch,jobs))
for r in receipts:
 f=p/r['file']
 if f.exists() and f.read_bytes()[:4]==b'%PDF':
  t=f.with_suffix('.txt'); q=subprocess.run(['pdftotext','-layout',str(f),str(t)],capture_output=True,timeout=20);r['text_file']=str(t.relative_to(p));r['text_status']=q.returncode
(p/'body-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n')
print(json.dumps(histories,indent=2));print(json.dumps(receipts,indent=2))
