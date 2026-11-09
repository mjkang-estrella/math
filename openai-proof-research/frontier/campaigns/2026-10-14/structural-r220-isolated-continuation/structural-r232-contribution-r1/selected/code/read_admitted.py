#!/usr/bin/env python3
"""Private local semantic display; exact manifest exceptions only; byte splitlines parser."""
from pathlib import Path
import sys,json,re,hashlib,datetime
R=Path(__file__).resolve().parents[2]
A=R.parent/'fresh-structural-discovery-r232'/'selected'
aliases=json.loads((R/'selected/private/aliases.json').read_bytes())
mode,key=sys.argv[1:3]; p=A/aliases[key]; b=p.read_bytes(); lines=b.splitlines(keepends=True)
off=[0]
for x in lines:off.append(off[-1]+len(x))
head=re.compile(rb'(^\s*(?:\\(?:sub)*section|\\begin\{(?:theorem|lemma|proposition|corollary)|[A-Z]\. |[0-9]+(?:\.[0-9]+)*[.\xE2\x80\xB2\']?\s+[A-Z]|(?:Theorem|Lemma|Proposition|Corollary|Remark|Definition)\s+[0-9]))')
editor=re.compile(rb'acknowledg|acknowleg|licen[sc]e|copyright|all rights|downloaded from|personal communication|private communication|pointed out to|the author thanks|we thank|would like to thank|grateful to|supported by|funded by|e-mail|email:|publisher|received [0-9]|accepted [0-9]',re.I)
if mode=='classify':
 print(key,'bytes',len(b),'lines',len(lines),'formfeeds',b.count(b'\x0c'))
 for i,l in enumerate(lines):
  if editor.search(l):print(i+1,off[i],off[i+1],'[EDITORIAL-CANDIDATE MASKED]')
  elif head.search(l):print(i+1,off[i],off[i+1],l.decode(errors='replace').strip()[:170])
else:
 start,end=map(int,sys.argv[3:5]);assert 1<=start<=end<=len(lines)
 masks=json.loads((R/'selected/private/masks.json').read_bytes()).get(key,[])
 print('READ',key,'LINES',start,end,'BYTES',off[start-1],off[end])
 for i in range(start-1,end):
  if any(lo<=i+1<=hi for lo,hi in masks): print('[MASKED editorial line '+str(i+1)+']')
  elif editor.search(lines[i]): print('[MASKED unresolved editorial candidate '+str(i+1)+']')
  else: print(lines[i].decode(errors='strict'),end='')
 rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'alias':key,'path':aliases[key],'file_sha256':hashlib.sha256(b).hexdigest(),'lines_inclusive':[start,end],'bytes_half_open':[off[start-1],off[end]],'masks':masks}
 with (R/'selected/private/semantic-reads.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
