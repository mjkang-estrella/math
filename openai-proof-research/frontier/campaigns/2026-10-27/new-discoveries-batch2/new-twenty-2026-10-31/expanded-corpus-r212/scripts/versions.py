import pathlib,re,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];out={}
for p in (D/'sources').glob('*.html'):
 if not re.match(r'\d{4}\.\d+\.html',p.name):continue
 a=p.stem;s=p.read_text();versions=sorted(set(re.findall(r'\[v(\d+)\]',s)),key=int);out[a]=versions
 for v in versions[:-1]:subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),f'{a}v{v}.pdf',f'https://arxiv.org/pdf/{a}v{v}'])
(D/'outputs/version-inventory.json').write_text(json.dumps(out,indent=2)+'\n')
