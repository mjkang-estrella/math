import pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];B=D.parent;ids=set(json.loads((D/'extracted.json').read_text()));out={}
for p in B.glob('*/results.json'):
 if p.parent==D:continue
 try:j=json.loads(p.read_text())
 except (ValueError,OSError):continue
 if isinstance(j,dict):
  for i in ids & j.keys():out.setdefault(i,[]).append({'file':str(p),'entry':j[i]})
(D/'history-exact.json').write_text(json.dumps(out,indent=2));print({i:[r['file'] for r in rows] for i,rows in out.items()})
