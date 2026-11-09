from run import *
import re
out=[]
for p in sorted((L/'primary').glob('*.txt')):
 a=sha(p);t=p.read_text(); lines=t.splitlines()
 chunks=[t[:3600]]
 for i,line in enumerate(lines):
  if re.search(r'^(Conjecture|Theorem|Problem|Question|1\.1\.|1\.2\.)',line.strip()):chunks.append('\n'.join(lines[max(0,i-2):i+16]))
 s='\n\n'.join(chunks)[:18000];assert sha(p)==a
 out.append({'path':str(p),'sha256':a,'excerpts':s})
 print('\nFILE '+p.name+'\n'+s[:8500])
dump('body-readings.json',out)
