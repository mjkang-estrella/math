H=json.loads((P/'history-hits.json').read_text()); out=[]
for h in H:
 obj=h['record']; matches={}
 if isinstance(obj,dict):
  for k,v in obj.items():
   if any(term in json.dumps(v) for term in h['matched']):matches[k]=v
 out.append(dict(path=h['path'],matched=h['matched'],records=matches));print(h['path']);print(json.dumps(matches,ensure_ascii=False)[:9000])
(P/'history-hits.json').write_text(json.dumps(out,indent=2))
allow=json.loads((P/'historical-results-allowlist.json').read_text())
for name in allow:
 if 'expanded-corpus-r323/results.json' in name:
  obj=json.loads(pathlib.Path(name).read_text());t=json.dumps(obj)
  import re
  print('REGISTRY URLS',sorted(set(re.findall(r'https[^\s"<>]+',t)))[:50])
