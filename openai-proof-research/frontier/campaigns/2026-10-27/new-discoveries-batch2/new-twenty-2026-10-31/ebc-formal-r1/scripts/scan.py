from pathlib import Path
import re, json, hashlib
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ebc-formal-r1')
forbidden={'sorry','admit','axiom','unsafe','partial','native_decide','ofReduceBool','bv_decide','implemented_by','extern'}
findings=[];hashes={}
for p in sorted((L/'src').glob('*.lean')):
 s=p.read_text();hashes[p.name]=hashlib.sha256(p.read_bytes()).hexdigest()
 # Nested Lean block comments, line comments, and quoted strings are not code.
 clean=[];i=0;depth=0
 while i<len(s):
  if depth:
   if s.startswith('/-',i):depth+=1;i+=2
   elif s.startswith('-/',i):depth-=1;i+=2
   else:i+=1
  elif s.startswith('/-',i):depth=1;i+=2;clean.append(' ')
  elif s.startswith('--',i):
   j=s.find('\n',i);i=len(s) if j<0 else j
  elif s[i]=='"':
   i+=1
   while i<len(s):
    if s[i]=='\\':i+=2
    elif s[i]=='"':i+=1;break
    else:i+=1
   clean.append(' ')
  else:clean.append(s[i]);i+=1
 tokens=re.findall(r'[A-Za-z_][A-Za-z_0-9]*',''.join(clean))
 bad=sorted(set(tokens)&forbidden)
 bad.extend(t for t in tokens if '_unsafe_rec' in t)
 if bad:findings.append({'file':p.name,'tokens':bad})
r={'pass':not findings,'findings':findings,'source_sha256':hashes,'module_count':len(hashes)}
(L/'logs/source-scan.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'source_scan_pass':not findings,'module_count':len(hashes)}))
assert not findings
