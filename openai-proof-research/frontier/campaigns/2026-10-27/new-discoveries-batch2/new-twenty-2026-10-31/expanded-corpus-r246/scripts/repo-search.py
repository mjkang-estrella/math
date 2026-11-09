import pathlib,json,urllib.parse,time,subprocess
D=pathlib.Path(__file__).resolve().parents[1];qs=['"1805.04888" lean','"local antimagic" lean','"Lau" "Shiu" lean','"Mobius ladder" lean'];entries=[]
for k,q in enumerate(qs):
 if k and 'api.github.com' in json.loads((D/'sources/denied.json').read_text()):break
 if k:time.sleep(8)
 u='https://api.github.com/search/repositories?q='+urllib.parse.quote(q)
 file=D/f'queue-search-{k}.json';file.write_text(json.dumps([(f'github-repository-search-{k}.json',u)]))
 subprocess.run(['python3','-I','-B',str(D/'scripts/fetch.py'),str(file)],check=True)
 p=D/f'sources/github-repository-search-{k}.json';rec=json.loads(p.with_name(p.name+'.receipt.json').read_text());e={'query':q,'receipt':str(rec),'hits':None}
 if p.exists():
  try:
   o=json.loads(p.read_text());e['hits']=o.get('total_count');e['repositories']=[x['full_name'] for x in o.get('items',[])]
  except ValueError:pass
 entries.append(e)
 if rec.get('status') in (403,429):break
(D/'repo-search-results.json').write_text(json.dumps(entries,indent=2))
