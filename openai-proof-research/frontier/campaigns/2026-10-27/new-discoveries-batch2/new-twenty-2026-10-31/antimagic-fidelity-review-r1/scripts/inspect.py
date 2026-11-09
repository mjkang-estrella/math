from pathlib import Path
import re,json,hashlib,zipfile
L=Path(__file__).resolve().parents[1];B=L.parent
H=lambda b:hashlib.sha256(b).hexdigest()
# Strip nested Lean comments, line comments and string/character literals conservatively.
def strip(s):
 out=[];i=0;level=0;string=False
 while i<len(s):
  if level:
   if s[i:i+2]=='/-':level+=1;i+=2
   elif s[i:i+2]=='-/':level-=1;i+=2
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif string:
   if s[i]=='\\':i+=2
   elif s[i]=='"':string=False;i+=1
   else:out.append('\n' if s[i]=='\n' else ' ');i+=1
  elif s[i:i+2]=='/-':level=1;i+=2
  elif s[i:i+2]=='--':
   j=s.find('\n',i);i=len(s) if j<0 else j
  elif s[i]=='"':string=True;i+=1
  else:out.append(s[i]);i+=1
 return ''.join(out)
scan={}
for p in sorted((L/'fresh').glob('*.lean')):
 clean=strip(p.read_text());hits=[]
 for i,line in enumerate(clean.splitlines(),1):
  if re.search(r'\b(sorry|admit|axiom|native_decide|ofReduceBool|implemented_by)\b',line):hits.append([i,line])
 scan[p.name]=hits
assert not any(scan.values()),scan
(L/'evidence/source-scan.json').write_text(json.dumps(scan,indent=2))
# All inherited manifests are checked against both their own lane and the final extracted source.
chain=[];bind={}
for lane in sorted(B.glob('antimagic-formal-r*')):
 for mf in sorted(lane.glob('*before.sha256'))+sorted(lane.glob('*after.sha256')):
  bind[str(mf)]=H(mf.read_bytes());count=0
  for line in mf.read_text().splitlines():
   m=re.match(r'^([a-f0-9]{64})\s+(.+\.lean)$',line)
   if not m:continue
   h,name=m.groups();name=Path(name).name
   p=lane/name;final=L/'fresh'/name
   assert H(p.read_bytes())==h,(p,h)
   assert H(final.read_bytes())==h,(mf,name,'final mismatch')
   count+=1
  chain.append({'manifest':str(mf),'checked_modules':count})
 for fn in ('source.zip','results.json'):
  p=lane/fn
  if p.exists():bind[str(p)]=H(p.read_bytes())
 # Independently read archive bytes without extracting or executing earlier scripts.
 a=lane/'source.zip'
 if a.exists():
  with zipfile.ZipFile(a) as z:
   count=0
   for inf in z.infolist():
    if inf.filename.endswith('.lean'):
     assert inf.file_size<20000000
     name=Path(inf.filename).name;f=L/'fresh'/name
     if f.exists():assert H(z.read(inf))==H(f.read_bytes()),(lane,name)
     count+=1
  chain.append({'archive':str(a),'checked_modules':count})
(L/'evidence/hash-chain.json').write_text(json.dumps({'chain':chain,'input_hashes':bind},indent=2))
# Bind source and corpus literal, including complete chunk and exact newline-bearing line.
c=B.parent/'lanes/pi-mathdb-full-corpus-inventory-r301/corpus/mathdb-normalized-chunk-0008.jsonl'
raw=c.read_bytes().splitlines(keepends=True)[3528];assert json.loads(raw)['mathdb_id']==354228
(L/'evidence/mathdb-354228.raw.jsonl').write_bytes(raw)
inputs=[c,B/'antimagic-root-ruling-r1.json',B/'expanded-corpus-r142/sources/354228.body.txt',B/'expanded-corpus-r142/sources/354228.html.html',B/'antimagic-review-r1/dl/episciences/fi9349.pdf']
(L/'evidence/additional-input-before.json').write_text(json.dumps({str(p):H(p.read_bytes()) for p in inputs},indent=2))
print('source scan PASS; manifest/archive identity PASS;',len(chain),'chain records; raw line hash',H(raw))
# Also check recorded archive digest receipts and the inter-branch merge pairs.
for lane in sorted(B.glob('antimagic-formal-r*')):
 a=lane/'source.zip'
 if a.exists():
  for name in ('source.sha256','source.zip.sha256'):
   receipt=lane/name
   if receipt.exists():
    expected=re.search(r'[0-9a-f]{64}',receipt.read_text())[0]
    assert expected==H(a.read_bytes()),receipt
lines=(L/'fresh/bridge-imports.sha256').read_text().splitlines()
assert len(lines)%2==0
for i in range(0,len(lines),2):
 h1=lines[i].split()[0];h2,name=lines[i+1].split()
 assert h1==h2==H((L/'fresh'/name).read_bytes())
r=json.loads((L/'fresh/results.json').read_text())
assert r['frozen_packet_sha256']==H((B/'antimagic-formal-r6a/source.zip').read_bytes())
assert r['bridge_packet_sha256']==H((B/'antimagic-formal-r4b/source.zip').read_bytes())
print('archive digest receipts and bridge pair manifest PASS')
