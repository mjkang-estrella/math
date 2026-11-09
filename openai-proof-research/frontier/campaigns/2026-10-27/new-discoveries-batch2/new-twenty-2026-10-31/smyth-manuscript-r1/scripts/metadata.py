from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parent.parent;E=R/'evidence'
f=(E/'smyth-formal-r1/src/Base.lean').read_text();d=(E/'expanded-corpus-r151/candidate-332037/Smyth1512Refutation.lean').read_text()
names=['U','rearr','psum','DomL','Dom','concat','Conjecture15'];out={}
for n in names:
 pat=r'^def '+n+r'\b.*?(?=\n\n|\Z)'
 a=re.search(pat,f,re.S|re.M).group();b=re.search(pat,d,re.S|re.M).group()
 out[n]={'identical':a==b,'sha256':hashlib.sha256(a.encode()).hexdigest()}
 assert a==b,n
mods=list((R/'packet-extracted/src').glob('*.lean'));assert len(mods)==48
rows=json.loads((R/'audit-certificate.json').read_text())['rows']
for label in ['S','T']:
 for i,count in enumerate(rows[label]):
  text=(R/f'packet-extracted/src/{label}{i:02}.lean').read_text()
  assert re.search(r'length = '+str(count)+r'\s*:=',text),(label,i,count)
formal=json.loads((E/'smyth-formal-r1/results.json').read_text())
raw=E/'expanded-corpus-r151/raw/332037.jsonl';assert len(raw.read_bytes().splitlines())==1
out['raw_line_sha256']=hashlib.sha256(raw.read_bytes()).hexdigest();out['modules']=len(mods);out['rows_match']=True
(R/'audit-correspondence.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
