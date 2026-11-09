f=P.parent/'expanded-corpus-r322/http-receipts.jsonl'
if f.is_file():
 for l in f.read_text().splitlines():
  r=json.loads(l)
  if any(x in r.get('url','') for x in ['github','leanpool']):print(r['url'])
