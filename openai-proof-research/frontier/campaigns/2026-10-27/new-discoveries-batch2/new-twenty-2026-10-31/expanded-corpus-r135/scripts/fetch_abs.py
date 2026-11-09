import urllib.request,json,hashlib,pathlib,datetime,re,sys
D=pathlib.Path(__file__).resolve().parents[1]
items=json.loads((D/'extracted.json').read_text()); rec=[]
seen=set()
for i,o in items.items():
 a=o['source_url'].split('/')[-1]
 if a in seen: continue
 seen.add(a); url='https://arxiv.org/abs/'+a
 r={'id':i,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source verification'}),timeout=18) as f:
   b=f.read(); r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest())
  (D/'sources'/f'abs-{a}.html').write_bytes(b); t=b.decode('utf8','replace')
  r['title']=re.sub(r'\s+',' ',re.search(r'<h1 class="title mathjax">.*?</span>(.*?)</h1>',t,re.S).group(1)).strip()
  r['authors']=re.findall(r'searchtype=author[^>]*>([^<]+)<',t)[:8]
  r['versions']=re.findall(r'<strong>\[(v\d+)\]</strong>\s*([^<]*)',t)
  m=re.search(r'Journal reference:</td>\s*<td[^>]*>(.*?)</td>',t,re.S); r['journal_ref']=m and re.sub(r'\s+',' ',m.group(1))
  m=re.search(r'class="tablecell comments mathjax">(.*?)</td>',t,re.S); r['comments']=m and re.sub(r'<[^>]+>|\s+',' ',m.group(1)).strip()
 except Exception as e: r['error']=str(e)
 rec.append(r); print(json.dumps(r,ensure_ascii=False),flush=True)
(D/'sources/receipts-abs.json').write_text(json.dumps(rec,indent=2,ensure_ascii=False)+'\n')
