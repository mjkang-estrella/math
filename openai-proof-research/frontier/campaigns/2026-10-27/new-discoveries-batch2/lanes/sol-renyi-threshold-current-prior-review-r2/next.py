exec(compile((__import__('pathlib').Path(__file__).parent/'fetch.py').read_text().split('for name,url in jobs:')[0], 'fetch-init','exec'))
head=json.loads((L/'omega-head.json').read_text())['sha']
print('OMEGA HEAD',head,flush=True)
jobs=[('omega-delta.json','https://api.github.com/repos/the-omega-institute/trureturing/compare/89cda9c274d1122b7676173296af3047c3b64cd1...'+head),('mm.pdf','https://arxiv.org/pdf/1710.00800')]
exec(compile((L/'fetch.py').read_text().split('for name,url in jobs:')[1].join(['for name,url in jobs:','']), 'fetch-loop','exec'))
import subprocess
for name in ['li','survey','mm']:
 if (L/(name+'.pdf')).exists():subprocess.run(['pdftotext','-layout',str(L/(name+'.pdf')),str(L/(name+'.txt'))],check=True)
for name in ['omega','openai']:
 d=json.loads((L/(name+'-head.json')).read_text());print(name,d['sha'],d['commit']['committer']['date'],len(d.get('files',[])))
if (L/'omega-delta.json').exists():
 d=json.loads((L/'omega-delta.json').read_text());print('DELTA',d.get('total_commits'),len(d.get('commits',[])),len(d.get('files',[])));print('\n'.join(f['filename'] for f in d.get('files',[])))
