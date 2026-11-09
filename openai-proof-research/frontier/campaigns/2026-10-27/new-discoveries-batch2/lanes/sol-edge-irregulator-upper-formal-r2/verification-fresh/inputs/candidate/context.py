import pathlib,json,re,hashlib,datetime
b=pathlib.Path(__file__).resolve().parent;p=b.parent
files=[p.parent/'ledger.json',p.parent/'prior-campaign-context.json',p.parent/'NEXT.md',p/'root-polyomino57-acceptance-r1/ACCEPTANCE-PRIOR-LIMITS.json']
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'inputs':{},'registry_matches':{}}
for f in files:
 d=f.read_bytes();out['inputs'][str(f)]={'sha256':hashlib.sha256(d).hexdigest()}
 if f.name.endswith('.json'):
  j=json.loads(d)
  if 'accepted' in j:out[f.name]=[{k:v for k,v in x.items() if k in ['number','title','source_target','scope']} for x in j['accepted']]
for f in [p/'sol-fresh-source-discovery-r57/sources/omega-Problems.json',p/'sol-polyomino57-source-prior-refresh-r3/live/omega-D5.json',p/'sol-fresh-source-discovery-r61/provenance.json']:
 if not f.exists():continue
 d=f.read_bytes();out['inputs'][str(f)]={'sha256':hashlib.sha256(d).hexdigest()}
 j=json.loads(d)
 if 'tree' in j:
  out['registry_matches'][str(f)]=[x for x in j['tree'] if re.search('irregular|bensmail|domination|alikhani|omar',x['path'],re.I)]
 else:out['reset_evidence']={k:v for k,v in j.items() if re.search('registry|reset|access',k,re.I)}
(b/'context-screen.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out.get('registry_matches'),indent=2))
