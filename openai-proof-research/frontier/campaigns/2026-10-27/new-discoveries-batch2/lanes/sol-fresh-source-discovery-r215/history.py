from work import *
def refresh():
 for fn in ['qualified-original-index.json','alias-refresh.json']:
  rows=json.loads((B/('lanes/sol-fresh-source-discovery-r212/'+fn)).read_text())['records'];seen={r['original'] for r in rows}
  if fn.startswith('qualified'):
   for n in [207,208,209]:
    p=B/f'lanes/sol-fresh-source-discovery-r{n}'/fn
    if not p.exists():continue
    for r in json.loads(p.read_text())['records']:
     if r['original'] not in seen:rows.append(r);seen.add(r['original'])
   for p in B.joinpath('lanes').glob('*/*'):
    if p.is_file() and p.parent!=L and p.name.lower() in ['summary.md','discovery.md','decision.md','proof.md','review.md'] and str(p.resolve()) not in seen:
     rows.append(dict(original=str(p.resolve()),sha256=None,snapshot_reference=None));seen.add(str(p.resolve()))
  changed=[]
  for i,r in enumerate(rows):
   old=r['sha256'];ref=r.get('snapshot_reference')
   if ref:assert sha(Path(ref).read_bytes())==old,ref
   p=Path(r['original'])
   if not p.exists():r['missing_live_original']=True;continue
   x=p.read_bytes();h=sha(x);r.update(previous=old,sha256=h,changed=h!=old)
   if h!=old:
    dest=f'changed/{fn[:5]}-{i}-{p.parent.name}-{p.name}';put(dest,x);assert sha(p.read_bytes())==h;r['snapshot_reference']=str(L/dest);changed.append(str(p))
  dump(fn,dict(utc=utc(),records=rows,changed=changed));print(fn,len(rows),len(changed))
def screen(terms,name):
 hits=[]
 for fn in ['qualified-original-index.json','alias-refresh.json']:
  for r in json.loads((L/fn).read_text())['records']:
   p=Path(r['snapshot_reference']);x=p.read_bytes();assert sha(x)==r['sha256'];s=x.decode(errors='replace').lower()
   h=[t for t in terms if t.lower() in s]
   if h:hits.append(dict(original=r['original'],snapshot_reference=str(p),sha256=r['sha256'],terms=h))
 dump(name,dict(utc=utc(),terms=terms,hits=hits));print('hits',len(hits));print(json.dumps(hits)[:13000])
if __name__=='__main__':
 if sys.argv[1]=='refresh':refresh()
 else:screen(sys.argv[3:],sys.argv[2])
