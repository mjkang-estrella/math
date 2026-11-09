from pathlib import Path
import sys,json,re,hashlib
ROOT=Path(__file__).resolve().parent
p=ROOT/'private/canonical'/sys.argv[2]
b=p.read_bytes(); lines=b.splitlines(keepends=True); starts=[0]
for l in lines:starts.append(starts[-1]+len(l))
if sys.argv[1]=='map':
 print('BOUNDARIES',sys.argv[2],len(b),'bytes',len(lines),'byte-parser lines')
 for i,l in enumerate(lines):
  s=l.decode('utf-8','replace')
  if re.search(r'\\(?:sub)*section\*?\{|\\(?:appendix|begin\{(?:theorem|lemma|proposition|corollary|remark|proof|abstract)|end\{(?:document|abstract))|\\(?:input|include)\{|\\(?:title|author|date|maketitle)|^#',s):print(i+1,starts[i],s.strip())
  if re.search(r'acknowl|acknowl?edg|thank|grateful|communicat|copyright|licen[cs]e|publisher|download|address|email|dedicat',s,re.I): print(i+1,starts[i],'[MASKED EDITORIAL CANDIDATE]')
else:
 spans=[tuple(map(int,r.split(':'))) for r in sys.argv[3:]]
 # half-open 1-based line boundaries, exact bytes using the same parser.
 rec=[]
 for a,z in spans:
  assert 1<=a<z<=len(lines)+1
  data=b[starts[a-1]:starts[z-1]]
  print(f'EXACT {sys.argv[2]} lines[{a},{z}) bytes[{starts[a-1]},{starts[z-1]}) SHA256 {hashlib.sha256(data).hexdigest()}')
  print(data.decode())
  rec.append({'path':sys.argv[2],'lines':[a,z],'bytes':[starts[a-1],starts[z-1]],'sha256':hashlib.sha256(data).hexdigest(),'mode':'semantic-display'})
 with (ROOT/'private/semantic-reads.jsonl').open('a') as f:
  for r in rec:f.write(json.dumps(r)+'\n')
