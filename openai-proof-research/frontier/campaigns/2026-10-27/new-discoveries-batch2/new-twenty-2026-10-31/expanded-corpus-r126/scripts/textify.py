import pathlib,subprocess,json
D=pathlib.Path(__file__).resolve().parents[1]
for p in sorted((D/'sources').glob('*.pdf')):
 r=subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],capture_output=True,text=True)
 print(p.name,r.returncode,r.stderr)
for n in ['omega','openai']:
 o=json.loads((D/f'sources/{n}-head.json').read_text());print(n,o['sha'])
