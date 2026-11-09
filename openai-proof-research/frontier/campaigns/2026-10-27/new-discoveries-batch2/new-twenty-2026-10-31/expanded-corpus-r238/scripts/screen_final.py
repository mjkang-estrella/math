import pathlib,json,re,hashlib
D=pathlib.Path(__file__).resolve().parents[1];terms=['352551','352593','352624','352761','352854','352971','355810','374657','345099','345186','345243','345516','345521','345595','345751','345790','345811','345841','345931','345943','2111.03877','2111.05489','2111.07131','2111.14617','2112.04115','2112.09619','2208.10475','2605.10276','high-order','highorder','antimagic','polygon','feedback','Bosek','neighborhoodideal','CMPP','heptagon','signuncertainty','Waring','elongated','eigenpolynomial','inversionsequence','hatguess','Gao','Toeplitz','handlebody']
out={}
for p in (D/'sources').glob('*complete.json'):
 t=json.loads(p.read_text());hits=[x['path'] for x in t.get('tree',[]) if any(a.lower() in x['path'].lower() for a in terms)];out[p.name]={'truncated':t.get('truncated'),'total_paths':len(t.get('tree',[])),'hits':hits}
for p in list((D/'sources').glob('pool-*'))+list((D/'sources').glob('lean-pool-candidates*')):
 if p.name.endswith('receipt.json'):continue
 ls=[{'line':n,'text':l} for n,l in enumerate(p.read_text(errors='replace').splitlines(),1) if any(a.lower() in l.lower() for a in terms)];out[p.name]=ls
for p in (D/'sources').glob('*head.json'):
 t=json.loads(p.read_text());out[p.name]={'sha':t.get('sha'),'date':t.get('commit',{}).get('committer',{}).get('date')}
(D/'registry-screen-final.json').write_text(json.dumps(out,indent=2)+'\n')
for k,v in out.items():
 if isinstance(v,dict):print(k,str(v)[:3500])
print('Lean Pool targeted hits',*[str((k,len(v))) for k,v in out.items() if isinstance(v,list)])
# Read entire shared ledger/context but keep a bounded lane-local snapshot summary.
for p in [D.parent/'ledger.json',D.parent.parent/'ledger.json',D.parent.parent/'prior-campaign-context.json']:
 t=json.loads(p.read_text());obj={'path':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'top_level_keys':list(t),'accepted':[{'id':x.get('mathdb_id'), 'title':x.get('title'), 'status':x.get('status')} for x in t.get('accepted',[])],'excluded':t.get('excluded',[])}
 (D/(p.parent.name+'-'+p.name+'.read-summary.json')).write_text(json.dumps(obj,indent=2)+'\n')
