import pathlib,sys,json,re
exec(compile((pathlib.Path(__file__).parent/'fetch.py').read_text().split("if sys.argv[1]=='sources':")[0],str(pathlib.Path(__file__).parent/'fetch.py'),'exec'))
for p in sorted((D/'sources').glob('abs-*.html')):
 aid=p.stem[4:]
 if '.' not in aid:continue
 versions=sorted(set(map(int,re.findall(r'\[v(\d+)\]',p.read_text()))))
 for v in versions[:-1]:fetch('https://arxiv.org/pdf/'+aid+'v'+str(v),aid+'v'+str(v)+'.pdf')
for key,repo in [('omega','the-omega-institute/trureturing'),('openai','openai/math')]:
 head=json.loads((D/f'sources/{key}-head.json').read_text())['sha']
 tree=json.loads((D/f'sources/{key}-tree.json').read_text())
 if tree.get('truncated'):
  for name in (['D5','Problems'] if key=='omega' else ['preprints']):
   fetch('https://api.github.com/repos/'+repo+'/git/trees/'+head+':'+name+'?recursive=1',key+'-'+name+'-tree.json')
for i in ['12491','14746']:
 s=(D/f'sources/abs-{i}.html').read_text();m=re.search(r'/content/serial-article-files/\d+',s)
 if m:fetch('https://ems.press'+m[0],i+'-source.pdf')
import subprocess
for p in sorted((D/'sources').glob('*.pdf')):
 if p.read_bytes().startswith(b'%PDF') and not p.with_suffix('.txt').exists():subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))])
