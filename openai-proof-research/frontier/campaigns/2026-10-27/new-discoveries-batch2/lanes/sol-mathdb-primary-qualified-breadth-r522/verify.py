#!/usr/bin/env python3
"""Independent read-only verification. Run under the fixed helper guard."""
from pathlib import Path
import json,hashlib,sys,datetime,itertools
from collections import Counter
P=Path(__file__).resolve().parent;L=P.parent;I=L/'root-mathdb-breadth-intake-r519';C=L/'pi-mathdb-full-corpus-inventory-r301'
def h(b):return hashlib.sha256(b).hexdigest()
def j(p):return json.loads(p.read_bytes())
def require(test,msg):
 if not test:raise ValueError(msg)
def check_bytes(b,e):
 require(len(b)==e.get('size',e.get('bytes')),'size mismatch');require(h(b)==e['sha256'],'hash mismatch')
def check(p,e):
 try:check_bytes(p.read_bytes(),e)
 except Exception as x:raise ValueError(str(p)+': '+str(x)) from x
def inventory(actual,m):
 names=[e['path'] for e in m['files']];require(len(names)==len(set(names)),'duplicate manifest entries');require(set(actual)-set(m['excluded_exact_paths'])==set(names),'extra/missing file')
def exact(root,m):
 inventory({str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()},m)
 for e in m['files']:check(root/e['path'],e)
def negatives():
 e={'size':3,'sha256':h(b'abc')};tested=[]
 for name,fn in [('hash',lambda:check_bytes(b'abd',e)),('size',lambda:check_bytes(b'abcd',e)),('extra-file',lambda:inventory({'a','unexpected'},{'files':[{'path':'a'}],'excluded_exact_paths':[]}))]:
  try:fn()
  except ValueError:tested.append(name)
  else:raise ValueError('negative accepted: '+name)
 return tested
def verify():
 m=j(P/'manifest.json');require(m['excluded_exact_paths']==['manifest.json','final-verification-receipt.json'],'unexpected exclusions');exact(P,m)
 refs=j(P/'flat-bindings.json');require(len({r['path'] for r in refs})==len(refs),'duplicate external refs')
 for r in refs:check(Path(r['path']),r)
 check(I/'manifest.json',{'sha256':'f4cd9614780cc82f8cd1ef3f11b1ca07e0e6d2b6ac85f2ec97eed91cc7530071','size':17938});exact(I,j(I/'manifest.json'))
 pairs=j(I/'bindings.json')
 for e in pairs:
  for k in ['original','copy']:check(Path(e[k]),e)
 cmcopy=I/'frozen/pi-mathdb-full-corpus-inventory-r301/manifest.json';require((C/'manifest.json').read_bytes()==cmcopy.read_bytes(),'original r301 manifest differs')
 cm=j(C/'manifest.json');chunks=[e for e in cm['files'] if e['path'].startswith('corpus/')];require(len(chunks)==20 and len(cm['frozen_inputs'])==8,'inventory counts')
 for e in chunks+cm['frozen_inputs']:check(C/e['path'],e)
 cov=j(I/'coverage-delta.json');require(len(cov)==4083,'coverage baseline')
 active=j(I/'active-breadth-reservations.json');seen=set();protected=set()
 for a in active:protected.update(a['protected_ids'])
 for a in active:
  ids=set(a['ids']);require(len(ids)==len(a['ids'])==50,'reservation count');require(not ids&seen and not ids&set(map(int,cov)) and not ids&protected,'reservation overlap');seen|=ids
 for a in active:require(set(a['other_active_reservations'])==seen-set(a['ids']),'other reservations')
 q=j(I/'queue-r522.json');res=j(I/'reserved-ids-r522.json');ids={r['mathdb_id'] for r in q};require(len(q)==len(ids)==50 and ids==set(res['ids']),'assigned50 mismatch')
 routing=[json.loads(x) for x in (I/'routing-queue.jsonl').open()];require(len(routing)==6000,'routing count');route={r['mathdb_id']:r for r in routing};require(len(route)==6000,'routing duplicates')
 for row in q:require(row==route[row['mathdb_id']],'queue metadata changed')
 ds=j(P/'dispositions.json');rs=j(P/'records.json');require(len(ds)==len(rs)==50,'payload50 count');require({d['mathdb_id'] for d in ds}==ids=={d['mathdb_id'] for d in rs},'payload IDs')
 found={}
 for e in chunks:
  p=C/e['path']
  for n,line in enumerate(p.open(),1):
   r=json.loads(line)
   if r['mathdb_id'] in ids:
    require(r['mathdb_id'] not in found,'duplicate corpus ID');found[r['mathdb_id']]=(str(p),n,r)
 require(len(found)==50,'missing originals')
 for d in ds+rs:
  p,n,r=found[d['mathdb_id']];require(d['corpus_chunk']==p and d['corpus_line']==n,'coordinates');require(d['statement']==r['statement'],'literal statement changed');require(d['statement_utf8_sha256']==h(r['statement'].encode('utf-8')),'literal UTF8 hash');require(d['canonical_record_sha256']==h(json.dumps(r,ensure_ascii=False,sort_keys=True,separators=(',',':')).encode('utf-8')),'canonical record hash')
  if 'record' in d:require(d['record']==r,'record payload differs')
 for d in ds:require(d['accepted_credit']==0 and d['current_registry_cleared'] is False,'unsupported acceptance')
 proposals=j(P/'proposals.json');require(len(proposals)==2<=3,'brief count')
 require({p['mathdb_id'] for p in proposals}<ids,'proposal outside lane')
 for name in ['source-provenance.json','version-provenance.json','closest-provenance.json','derivative-bindings.json']:
  for e in j(P/name):
   if 'path' in e:check(Path(e['path']),e)
 # Re-evaluate exact finite witnesses without executing child/upstream code.
 def sc(pi):
  st=[];o=[]
  for x in pi:
   while any(t[i]<t[k]<t[k+1] for t in [[x]+st] for i in range(len(t)) for k in range(i+1,len(t)-1)):o.append(st.pop(0))
   st.insert(0,x)
  return tuple(o+st)
 require(sc((5,1,4,3,6,2))==(6,3,2,4,1,5),'source convention example')
 w=j(P/'witnesses.json');c=Counter(sc(p) for p in itertools.permutations(range(1,6)));require(sorted(set(c.values()),reverse=True)[:2]==[8,5],'n5 fibers')
 for e in w['stack_n5_second5_outputs']:
  target=tuple(e['output']);actual={p for p in itertools.permutations(range(1,6)) if sc(p)==target};require(actual=={tuple(p) for p in e['preimages']} and len(actual)==5,'n5 exact witness')
 t=w['stack_n8_tie'];a=tuple(t['alternative']);b=tuple(t['named']);fa=set();fb=set()
 for pi in itertools.permutations(range(1,9)):
  out=sc(pi)
  if out==a:fa.add(pi)
  if out==b:fb.add(pi)
 require(a!=b and len(fa)==len(fb)==64 and fa=={tuple(p) for p in t['alternative_fiber']} and fb=={tuple(p) for p in t['named_fiber']},'n8 tie witness')
 d=w['ball_n4']['distance_rank_matrix'];require(len({d[i][k] for i in range(4) for k in range(i+1,4)})==6 and all(d[i][k]==d[k][i] and (d[i][k]==0)==(i==k) for i in range(4) for k in range(4)),'ordinal matrix')
 balls={tuple(x for x in range(4) if d[c][x]<=r) for c in range(4) for r in range(7)};require(len(balls)==9 and balls=={tuple(b) for b in w['ball_n4']['balls']},'nine balls')
 return {'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','scientific_acceptance':False,'manifest':{'sha256':h((P/'manifest.json').read_bytes()),'size':(P/'manifest.json').stat().st_size},'literal_reviews':50,'family_briefs':2,'credit':0,'external_flat_bindings':len(refs),'intake_original_copy_pairs':len(pairs),'original_chunks':20,'frozen_inputs':8,'intake_exact_payload':True,'reservation_disjointness':True,'independent_witness_recalculation':True,'negative_rejections':negatives(),'current_registry':'HOLD','counts':{'additional':9,'total':39,'next':40}}
try:print(json.dumps(verify(),indent=2))
except Exception as e:print(json.dumps({'integrity':'FAIL','error':str(e)}));sys.exit(1)
