import pathlib,json,re,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];args=[];out={}
for name,aid in [('old-univalent','1712.06035'),('old-covariance','1709.09011')]:
 s=(D/f'sources/{name}-abs.body').read_text();vs=sorted(set(re.findall(re.escape(aid)+r'v(\d+)',s)),key=int);out[aid]=vs
 for v in vs:args+=[name+'-v'+v,'https://arxiv.org/pdf/'+aid+'v'+v]
(D/'outputs/older-source-versions.json').write_text(json.dumps(out,indent=2));subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),*args])
