import json,hashlib,subprocess,time,re,sys,pathlib,datetime,html
D=pathlib.Path(__file__).resolve().parents[1]
ex=json.loads((D/'extracted.json').read_text())
rec={}
for i,o in ex.items():
    aid=o['source_url'].split('/abs/')[1]
    out=D/f'sources/abs-{aid}.html'
    if not out.exists():
        r=subprocess.run(['curl','-sS','-L','-A','research-bot/1.0','-o',str(out),'-w','%{http_code}','https://arxiv.org/abs/'+aid],capture_output=True,text=True,timeout=60)
        code=r.stdout; time.sleep(3)
    else: code='cached'
    b=out.read_bytes(); s=b.decode('utf8','replace')
    t=re.search(r'<h1 class="title mathjax"><span class="descriptor">Title:</span>(.*?)</h1>',s,re.S)
    vers=re.findall(r'<strong>\[v(\d+)\]</strong>\s*(.*?)\s*\(',s)
    jr=re.search(r'<td class="tablecell jref">(.*?)</td>',s,re.S)
    cm=re.search(r'<td class="tablecell comments mathjax">(.*?)</td>',s,re.S)
    au=re.search(r'<div class="authors">(.*?)</div>',s,re.S)
    rec[i]={'arxiv':aid,'http':code,'sha256':hashlib.sha256(b).hexdigest(),'utc':datetime.datetime.utcnow().isoformat(),
      'title':html.unescape(re.sub('<.*?>','',t.group(1)).strip()) if t else None,
      'authors':html.unescape(re.sub('<.*?>','',au.group(1)).replace('Authors:','').strip()) if au else None,
      'versions':vers,'journal_ref':html.unescape(re.sub('<.*?>','',jr.group(1)).strip()) if jr else None,
      'comments':html.unescape(re.sub('<.*?>','',cm.group(1)).strip()) if cm else None}
    print(i,json.dumps(rec[i],ensure_ascii=False))
(D/'sources/abs-receipts.json').write_text(json.dumps(rec,indent=1,ensure_ascii=False)+'\n')
