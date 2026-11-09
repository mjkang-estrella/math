#!/usr/bin/env python3
import argparse,hashlib,json,stat,datetime,re
from pathlib import Path
ROOT=Path(__file__).resolve().parent
AUTHOR=ROOT.parent/'fresh-structural-discovery-r236'
def read(name):
 entries=json.loads((ROOT/'private/author-baseline.json').read_bytes())['entries']
 row=next((r for r in entries if r['path']==name),None)
 if row is None: raise ValueError('Not an exactly admitted author path')
 p=AUTHOR/name
 for q in [p,*p.parents]:
  if q==AUTHOR.parent: break
  if q.is_symlink(): raise ValueError('symlink')
 b=p.read_bytes()
 assert len(b)==row['bytes'] and hashlib.sha256(b).hexdigest()==row['sha256']
 assert f"{stat.S_IMODE(p.stat().st_mode):04o}"==row['mode']
 return b,b.splitlines(keepends=True)
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('path');ap.add_argument('--start',type=int,default=1);ap.add_argument('--stop',type=int);ap.add_argument('--classify',action='store_true');ap.add_argument('--omit',default='');a=ap.parse_args()
 b,ls=read(a.path);stop=a.stop or len(ls);assert 1<=a.start<=stop<=len(ls)
 omit=set()
 for item in a.omit.split(','):
  if item:
   nums=[int(x) for x in item.split('-')];omit.update(range(nums[0],nums[-1]+1))
 offsets=[0]
 for l in ls: offsets.append(offsets[-1]+len(l))
 print(f'FILE {a.path} total_lines={len(ls)} selected={a.start}:{stop} bytes=[{offsets[a.start-1]},{offsets[stop]})')
 if a.classify:
  for i,l in enumerate(ls,1):
   st=l.decode('utf-8').strip()
   if re.search(r'acknow|acknowl|licen[cs]|copyright|downloaded|communicat|thank|grateful|visiting|supported|e-mail|email|address|publisher|date:|author:|arxiv:',st,re.I): print(i,offsets[i-1],'MASK:editorial-candidate')
   elif re.match(r'^(#{1,6} |\\(?:sub)*section|\\(?:begin\{(?:theorem|lemma|proposition|corollary|remark)|input)|(?:[0-9]+[. ]|[A-Z][. ]|Theorem |Lemma |Proposition |Corollary |Remark |Proof|References))',st):print(i,offsets[i-1],st[:160])
 else:
  for i in range(a.start,stop+1):
   if i not in omit:print(f'{i}: '+ls[i-1].decode('utf-8').rstrip('\r\n'))
 rec={'path':a.path,'sha256':hashlib.sha256(b).hexdigest(),'start':a.start,'stop':stop,'bytes':[offsets[a.start-1],offsets[stop]],'omitted':sorted(omit),'classification_only':a.classify,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 with (ROOT/'private/reviewer-reads.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
