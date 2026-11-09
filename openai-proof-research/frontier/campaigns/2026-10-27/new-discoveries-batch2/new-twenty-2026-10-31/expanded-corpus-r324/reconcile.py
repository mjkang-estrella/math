V=json.loads((P/'provenance.json').read_text()); ids=set(V)
allow=json.loads((P/'historical-results-allowlist.json').read_text())
hits=[]; inventory=[]
for name in allow:
 if 'crown-vnumber-' in name or 'crim-conway-source-qualification-r1' in name:continue
 f=pathlib.Path(name)
 if not f.is_file():continue
 b=f.read_bytes(); inventory.append(dict(path=name,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),depth='bounded ID/title/source-family reconciliation'))
 t=b.decode()
 terms=[k for k in ids if k in t]
 terms += [v['parsed']['source_url'].split('/')[-1] for v in V.values() if v['parsed']['source_url'].split('/')[-1] in t]
 if terms:
  obj=json.loads(t); hits.append(dict(path=name,matched=terms,record=obj));print(name,terms,json.dumps(obj)[:10000])
(P/'history-hits.json').write_text(json.dumps(hits,indent=2))
(P/'history-read-inventory.json').write_text(json.dumps(inventory,indent=2))
for name in ['ledger.json','STATUS.md']:
 f=P.parent/name
 if not f.exists():f=P.parent.parent/name
 if f.exists():
  t=f.read_text(); lines=[line for line in t.splitlines() if ('52' in line or '60' in line) and len(line)<250]
  print(name,lines[:8])
