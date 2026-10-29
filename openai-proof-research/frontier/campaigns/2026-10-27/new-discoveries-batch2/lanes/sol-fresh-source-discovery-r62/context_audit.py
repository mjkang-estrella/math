import pathlib,json,hashlib,re,datetime
P=pathlib.Path(__file__).resolve().parent;B=P.parent.parent;R=B.parents[3]
rows=[]
for f in [B/'AGENTS.md',B/'NEXT.md',B/'ledger.json',B/'prior-campaign-context.json',P.parent/'root-polyomino57-acceptance-r1/ACCEPTANCE-PRIOR-LIMITS.json']:
 d=f.read_bytes();obj=json.loads(d) if f.suffix=='.json' else None
 row=dict(path=str(f),sha256=hashlib.sha256(d).hexdigest(),bytes=len(d))
 if isinstance(obj,dict):row['keys']=list(obj);row['accepted']=[{k:v for k,v in x.items() if k in ['number','title','source_target']} for x in obj.get('accepted',[])]
 rows.append(row)
pat=re.compile('kalmykov|turan|turán|hypergeometric|gamma.ratio|pochhammer',re.I)
for f in [P.parent/'sol-fresh-source-discovery-r57/sources'/x for x in ['omega-D5.json','omega-Problems.json','openai-head.json','aim-head.json','count-head.json']]:
 d=f.read_bytes();obj=json.loads(d);paths=[x['path'] for x in obj.get('tree',[])] if isinstance(obj,dict) else []
 rows.append(dict(path=str(f),sha256=hashlib.sha256(d).hexdigest(),cached_only=True,truncated=obj.get('truncated') if isinstance(obj,dict) else None,matches=[s for s in paths if pat.search(s)],note='Lexical path screen only; not body clearance. r57 D5 is Blueprint markdown, NOT Lean.'))
(P/'context-audit.json').write_text(json.dumps(rows,indent=2));print(json.dumps([{'path':r['path'],'matches':r.get('matches')} for r in rows if 'matches'in r],indent=2))
