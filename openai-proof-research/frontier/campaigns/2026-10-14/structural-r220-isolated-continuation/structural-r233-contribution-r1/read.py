from pathlib import Path
import argparse,hashlib,json,datetime,re
O=Path(__file__).resolve().parent
B=json.loads((O/'original-baseline.json').read_bytes())
A=Path(B['root'])
ENT={e['path']:e for e in B['entries']}
p=argparse.ArgumentParser();p.add_argument('name');p.add_argument('--start',type=int);p.add_argument('--end',type=int);p.add_argument('--classify',action='store_true');a=p.parse_args()
assert a.name in ENT
b=(A/a.name).read_bytes();assert hashlib.sha256(b).hexdigest()==ENT[a.name]['sha256']
ls=b.splitlines(keepends=True);ofs=[0]
for x in ls:ofs.append(ofs[-1]+len(x))
enc='latin1' if '/DT12/' in a.name else 'utf8'
markers=[]
for i,l in enumerate(ls):
 s=l.decode(enc)
 editorial=re.search(r'acknowl|ackow|acknol|private communication|personal communication|copyright|license|licence|supported by (?:the|a|grant)|funded by|\\(?:author|address|email|thanks|maketitle|documentclass|bibliograph|title)\b',s,re.I)
 heading=re.search(r'\\(?:sub)*section\*?\{|\\(?:begin\{(?:theorem|lemma|proposition|corollary|remark|proof)|end\{(?:theorem|lemma|proposition|corollary|remark|proof))\}',s)
 if editorial or heading:markers.append((i+1,ofs[i],ofs[i+1],'EDITORIAL-MASK' if editorial else s.strip()))
if a.classify:
 print(json.dumps({'name':a.name,'bytes':len(b),'lines':len(ls),'encoding':enc,'markers':markers},ensure_ascii=False));raise SystemExit
lo=a.start or 1;hi=a.end or len(ls);assert 1<=lo<=hi<=len(ls)
protected='private-primary/' in a.name or 'private-source/' in a.name
if protected:
 approved=json.loads((O/'approved-ranges.json').read_bytes());assert [a.name,lo,hi] in approved
masked={i for i,x,y,s in markers if s=='EDITORIAL-MASK'} if protected else set()
print(f'{a.name} L{lo}-{hi} bytes[{ofs[lo-1]},{ofs[hi]})')
for i in range(lo-1,hi):
 print(f'{i+1}: '+('[EDITORIAL-MASK]\n' if i+1 in masked else ls[i].decode(enc)),end='')
with (O/'reads.jsonl').open('a') as f:f.write(json.dumps({'name':a.name,'lines':[lo,hi],'bytes':[ofs[lo-1],ofs[hi]],'sha256':hashlib.sha256(b).hexdigest(),'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'masked_lines':[i for i in masked if lo<=i<=hi]})+'\n')
