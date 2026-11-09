import json,pathlib,re,sys,subprocess,hashlib
D=pathlib.Path(__file__).resolve().parents[1]
for p in sorted((D/'sources').glob('*/receipt.json')):
 r=json.loads(p.read_text());b=p.parent/'body'
 if r.get('status')!=200:continue
 if '/abs/' in r['url']:
  s=b.read_text();v=re.findall(r'\[v\d+\].{0,180}',s);print(r['url'],re.findall('<title>(.*?)</title>',s),v)
  print(re.findall(r'<td class="tablecell jref">(.*?)</td>',s,re.S))
 if '/pdf/' in r['url'] and b.read_bytes().startswith(b'%PDF'):
  out=D/'outputs'/(r['url'].split('/')[-1]+'.txt')
  if not out.exists():subprocess.run(['pdftotext','-layout',str(b),str(out)],check=True)
