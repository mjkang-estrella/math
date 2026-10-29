import json,pathlib,subprocess
L=pathlib.Path(__file__).resolve().parent
for n in ['omega-head','openai-head']:
 d=json.loads((L/'sources'/f'{n}.json').read_text())[0];print(n,d['sha'],d['commit']['committer']['date'])
d=json.loads((L/'sources/moment-openalex.json').read_text());print('MOMENT LOCATIONS',json.dumps(d.get('locations'),indent=2))
subprocess.run(['pdftotext','-layout',str(L/'sources/stover.pdf'),str(L/'sources/stover.txt')],check=True)
