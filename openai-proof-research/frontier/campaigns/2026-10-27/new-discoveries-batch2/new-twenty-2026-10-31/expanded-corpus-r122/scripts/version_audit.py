import pathlib,re,json,hashlib
D=pathlib.Path(__file__).resolve().parents[1];vs=json.loads((D/'versions.json').read_text());out={}
for a,vv in vs.items():
 rows=[]
 for v in vv:
  p=D/f'sources/{a}v{v}.txt';pdf=p.with_suffix('.pdf');s=p.read_text() if p.exists() else '';lines=s.splitlines();hits=[]
  for i,l in enumerate(lines):
   if re.search(r'Conjecture [0-9]|Problem [0-9]|withdraw|retract|removed.*conjecture',l,re.I):hits.append({'line_1based':i+1,'context':'\n'.join(lines[max(0,i-2):i+9])})
  rows.append({'version':v,'pdf_sha256':hashlib.sha256(pdf.read_bytes()).hexdigest() if pdf.exists() else None,'text_sha256':hashlib.sha256(s.encode()).hexdigest() if s else None,'passages':hits,'review_depth':'version-specific statement/retraction scan; not a claim of complete proof-body reading'})
 out[a]=rows
(D/'outputs/all-version-audit.json').write_text(json.dumps(out,indent=2,ensure_ascii=False));print('sources',len(vs),'versions',sum(map(len,vs.values())),'missing',[(a,r['version']) for a,rows in out.items() for r in rows if not r['pdf_sha256'] or not r['text_sha256']])
