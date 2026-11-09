import pathlib,json,re,subprocess,html
D=pathlib.Path(__file__).resolve().parents[1];out={}
for i,v in json.loads((D/'extracted.json').read_text()).items():
 s=(D/f'sources/{i}-abs.body').read_text();a=v['source_url'].split('/')[-1];vs=sorted(set(re.findall(a+r'v(\d+)',s)),key=int)
 # explicit history links only; no arbitrary v matches
 out[i]={'versions':vs,'doi':re.findall(r'name="citation_doi" content="([^"]+)',s),'authors':re.findall(r'name="citation_author" content="([^"]+)',s)}
 print(i,vs,out[i]['authors'],out[i]['doi'])
 for ver in vs:
  subprocess.run(['python3','-I',str(D/'scripts/fetch.py'),f'{i}-v{ver}-pdf',f'https://arxiv.org/pdf/{a}v{ver}'],check=True)
(D/'outputs/versions.json').write_text(json.dumps(out,indent=2))
