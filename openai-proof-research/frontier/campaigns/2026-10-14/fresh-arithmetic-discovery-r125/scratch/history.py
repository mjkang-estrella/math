import sys,signal,json,re,os,hashlib
from pathlib import Path
from guard import ROOT,OWN,reason
signal.alarm(150)
query=re.compile(r'finite.field|prime.field|Berlekamp|Ronyai|Rónyai|Allombert|Wedderburn|deterministic.{0,50}factori[sz]|factori[sz].{0,50}deterministic|nilpotent.{0,30}algebra|algebra.{0,30}nilpotent',re.I)
rec={'query':query.pattern,'admitted':[],'omissions':[],'errors':[],'hits':[]}
# Restrict initial descent to authored project work; source and administrative roots excluded prospectively.
for area in ['frontier','campaigns','iterations','experiments','proposals','scouts','notes','findings']:
 base=ROOT/area
 if not base.is_dir():continue
 for dp,ds,fs in os.walk(base,topdown=True,followlinks=False):
  p=Path(dp)
  keep=[]
  for d in sorted(ds):
   x=p/d;why=reason(x)
   if why:rec['omissions'].append({'path':str(x.relative_to(ROOT)),'reason':why,'kind':'directory'})
   else:keep.append(d)
  ds[:]=keep
  for f in sorted(fs):
   x=p/f;why=reason(x)
   if why:rec['omissions'].append({'path':str(x.relative_to(ROOT)),'reason':why,'kind':'file'});continue
   try:
    b=x.read_bytes();s=b.decode('utf-8')
   except (OSError,UnicodeError) as e:rec['errors'].append({'path':str(x.relative_to(ROOT)),'error':str(e)[:180]});continue
   entry={'path':str(x.relative_to(ROOT)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()};rec['admitted'].append(entry)
   hits=[{'line':i,'text':l} for i,l in enumerate(s.splitlines(),1) if query.search(l)]
   if hits:rec['hits'].append(dict(entry,matches=hits))
(OWN/'private/history-navigation.json').write_text(json.dumps(rec,indent=2,ensure_ascii=False)+'\n')
print({k:len(v) for k,v in rec.items() if isinstance(v,list)})
for h in rec['hits']:
 print(h['path'],[(x['line'],x['text'][:260]) for x in h['matches'][:2]])
