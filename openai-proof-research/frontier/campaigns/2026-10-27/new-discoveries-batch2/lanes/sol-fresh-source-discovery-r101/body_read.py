from pathlib import Path
import json,re,hashlib,datetime
P=Path(__file__).resolve().parent
ranges={'primary.txt':[(140,240),(300,458)],'classical.txt':[(175,229)],'survey.txt':[(2070,2125)],'survey-current.txt':[(2260,2312),(3045,3060)],'sg-original.txt':[(1,35)],'sg-successor.txt':[(680,746)]}
out=[]
for n,rs in ranges.items():
 f=P/'sources'/n;lines=f.read_text().splitlines();print('\nFILE',n)
 parts=[]
 for a,b in rs:
  parts.append(dict(start=a,end=b,text='\n'.join(lines[a-1:b])));print(parts[-1]['text'])
 out.append(dict(file='sources/'+n,sha256=hashlib.sha256(f.read_bytes()).hexdigest(),ranges=parts))
for f in sorted((P/'sources').glob('omega-relevant-*.txt')):
 s=f.read_text();parts=[l for l in s.splitlines() if re.search('theorem|Theorem|claim|Resolves|Conjecture|result|Definition',l)];out.append(dict(file='sources/'+f.name,sha256=hashlib.sha256(f.read_bytes()).hexdigest(),statement_lines=parts));print('\n',f.name,'\n','\n'.join(parts)[:7500])
(P/'body-read.json').write_text(json.dumps(dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sources=out),indent=2))
