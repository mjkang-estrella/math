import pathlib,subprocess,json,re
L=pathlib.Path(__file__).resolve().parents[1];(L/'text').mkdir(exist_ok=True)
for p in (L/'http').glob('*pdf/body'):
 if p.read_bytes()[:4]==b'%PDF':subprocess.run(['pdftotext','-layout',str(p),str(L/'text'/(p.parent.name+'.txt'))],check=True)
terms=['chocolate','johnson','heffter','cluster','cayley','hochstatt','hochstätt','jewel','freiman','turan','turán','hanoi','palindrom','resistance','spectral-pair','seifert']
out={}
for name in ['openai','pool','omega']:
 t=json.loads((L/'http'/f'{name}-tree/body').read_text());out[name]={'truncated':t.get('truncated'),'hits':[x['path'] for x in t['tree'] if any(w in x['path'].lower() for w in terms)]}
out['pool_raw_hits']={}
for p in (L/'http').glob('poolraw-*/body'):
 out['pool_raw_hits'][p.parent.name]=[{'line':i,'text':s} for i,s in enumerate(p.read_text().splitlines(),1) if any(w in s.lower() for w in terms)]
(L/'registry-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='pool_raw_hits'},indent=2)[:6500])
