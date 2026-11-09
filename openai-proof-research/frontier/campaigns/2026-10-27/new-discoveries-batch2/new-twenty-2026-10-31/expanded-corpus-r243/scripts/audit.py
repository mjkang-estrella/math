import pathlib,json,re,hashlib
L=pathlib.Path(__file__).resolve().parents[1];out={}
for p in sorted((L/'sources').glob('*pdf/text.txt')):
 lines=p.read_text().splitlines();out[str(p.relative_to(L))]=[{'line':i+1,'label':s.strip(),'context':'\n'.join(lines[max(0,i-1):i+7])} for i,s in enumerate(lines) if re.match(r'^Example\s|^\s*Figure\s+\d|^\s*Fig\.\s*\d',s)]
(L/'evidence/printed-examples-and-figures.json').write_text(json.dumps(out,indent=2))
rows=json.loads((L/'evidence/exact-records.json').read_text())
for k,v in rows.items():v['statement_utf8_sha256']=hashlib.sha256(v['record']['statement'].encode()).hexdigest()
(L/'evidence/provenance.json').write_text(json.dumps({k:{a:b for a,b in v.items() if a!='record'} for k,v in rows.items()},indent=2))
print('source figure inventories',len(out))
