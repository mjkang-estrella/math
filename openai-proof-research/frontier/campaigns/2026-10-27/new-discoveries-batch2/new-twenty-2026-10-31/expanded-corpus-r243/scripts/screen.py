import pathlib,json,re,hashlib
L=pathlib.Path(__file__).resolve().parents[1];terms=['1907.06235','1907.10816','1907.13360','1908.00081','1908.02385','1908.03914','1908.06624','1908.07658','1908.08647','1909.03504','1909.13143','1910.03038','1910.13244','1910.13549','1910.13912','1911.00207','1911.08686','1911.11713','1911.13151','antipower','naples','wenzel','postnikov','reticulation','graver','rainbow','t-filter','xiang','garg','bhanja','krattenthaler','hendriksen','ryser']
out={}
for p in (L/'sources').glob('leanpool-file-*/body'):
 s=p.read_text();hits=[{'line':i,'text':line[:800]} for i,line in enumerate(s.splitlines(),1) if any(t.lower() in line.lower() for t in terms)]
 if hits:out[str(p.relative_to(L))]=hits
for p in (L/'sources').glob('*-tree/body'):
 x=json.loads(p.read_text());paths=[r['path'] for r in x.get('tree',[])];out[str(p.relative_to(L))]={'truncated':x.get('truncated'),'hits':[p for p in paths if any(t.lower() in p.lower() for t in terms)]}
(L/'evidence/registry-screen.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2)[:13000])
