import pathlib,re,json,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1]; out={}
for p in sorted((D/'sources').glob('*.abs')):
 s=p.read_text(); h=s.split('Submission history')[1].split('full-text')[0]
 vs=sorted(set(re.findall(r'\[v(\d+)\]',h)),key=int);out[p.stem]=vs
 for v in vs[:-1]:
  name=p.stem+'v'+v+'.pdf'
  subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),name,'https://arxiv.org/pdf/'+p.stem+'v'+v],check=True)
(D/'outputs/source-versions.json').write_text(json.dumps(out,indent=2)+'\n')
print(out)
