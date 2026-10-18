#!/usr/bin/env python3
"""Query sealed pointers. All automatic matches remain unread unless adjudicated."""
import argparse,json,re,hashlib
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--family',action='append',required=True);p.add_argument('--root',type=Path);p.add_argument('--pattern');p.add_argument('--output',type=Path);a=p.parse_args()
b=Path(__file__).resolve().parent;j=json.loads((b/'history-index.json').read_text());ad=json.loads((b/'history-adjudications.json').read_text()) if (b/'history-adjudications.json').exists() else {}
out={}
for f in a.family:
 f=f.zfill(3);v=j['families'][f]
 out[f]={'name':v['name'],'papers':v['papers'],'status':ad.get(f,{'status':'authored-match-unread' if v['authored_matches'] else 'retrieved-or-referenced-only' if v['reference_matches'] else 'no-match-in-bounded-index; NOT CLEARANCE'}),'authored_matches':v['authored_matches'],'reference_only_matches':v['reference_matches']}
if a.pattern:
 if a.root is None:raise SystemExit('--pattern requires --root')
 hits=[]
 for x in j['artifacts']:
  if x['class']!='authored-note':continue
  q=a.root/x['path'];raw=q.read_bytes()
  if hashlib.sha256(raw).hexdigest()!=x['sha256']:raise SystemExit('history input drift: '+x['path'])
  for n,l in enumerate(raw.decode().splitlines(),1):
   if re.search(a.pattern,l,re.I):hits.append({'path':x['path'],'line':n,'text':l})
 out['broader_keyword_search']={'pattern':a.pattern,'matches':hits}
s=json.dumps(out,indent=2,ensure_ascii=False)+'\n'
if a.output:a.output.write_text(s)
else:print(s,end='')
