r=json.loads((P/'reservation.json').read_text());jwrite('fetch-primary.json',[(x['source_url'].split('/')[-1]+'.html',x['source_url'].replace('/abs/','/html/')) for x in {v['source_url']:v for v in r['rows']}.values()])
allow=json.loads((P/'historical-results-allowlist.json').read_text()); matches=[]; inventory=[]
for x in allow:
 if any(z in x.lower() for z in ['crown','transitive-bunkbed-prefix-helpers-formal-pi-r5']):continue
 f=pathlib.Path(x)
 if not f.is_file():inventory.append({'path':x,'missing':True});continue
 b=f.read_bytes();inventory.append({'path':x,'sha256':h(b),'bytes':len(b),'depth':'ID/source/title-family reconciliation only'})
 text=b.decode('utf-8','replace'); keys=[str(v) for v in r['ids']]+[v['source_url'].split('/')[-1] for v in r['rows']]
 for key in keys:
  for m in list(re.finditer(re.escape(key),text))[:3]:matches.append({'path':x,'key':key,'excerpt':text[max(0,m.start()-150):m.end()+650]})
jwrite('history-inventory.json',inventory);jwrite('history-matches.json',matches);print(json.dumps(matches,ensure_ascii=False))
for k,v in json.loads((P/'bindings.json').read_text()).items():
 print(k,v['parsed']['statement']);v['statement_utf8_sha256']=h(v['parsed']['statement'].encode())
jwrite('bindings.json',json.loads((P/'bindings.json').read_text()) | {})
