import resource
resource.setrlimit(resource.RLIMIT_AS,(480*1024**2,480*1024**2))
import urllib.request, urllib.error, json, hashlib, datetime
from pathlib import Path
out=Path(__file__).parent
rows=[]
def get(url,name):
    row={'url':url,'accessed_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        req=urllib.request.Request(url,headers={'User-Agent':'public-mathematical-research/1.0'})
        with urllib.request.urlopen(req,timeout=35) as r: data=r.read(); row['status']=r.status
        (out/name).write_bytes(data);row.update(file=name,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
        rows.append(row)
        return data
    except Exception as e:
        row['error']=str(e);rows.append(row);return None
for ident in ['2608.23006','2609.29531']:
    get('https://arxiv.org/abs/'+ident,ident+'-abs.html')
for repo in ['openai/math','the-omega-institute/trureturing']:
    stem=repo.replace('/','-')
    raw=get('https://api.github.com/repos/'+repo+'/commits/HEAD',stem+'-head.json')
    if not raw: continue
    head=json.loads(raw)['sha']
    for file in (['CONTENTS.md'] if repo=='openai/math' else ['README.md']):
        get(f'https://raw.githubusercontent.com/{repo}/{head}/{file}',stem+'-'+file)
    raw=get(f'https://api.github.com/repos/{repo}/git/trees/{head}',stem+'-root.json')
    if not raw: continue
    for item in json.loads(raw)['tree']:
        if item['path'] in ['preprints','Problems','Blueprint','D5']:
            get(f'https://api.github.com/repos/{repo}/git/trees/{item["sha"]}?recursive=1',stem+'-'+item['path']+'-tree.json')
(out/'retrieval.json').write_text(json.dumps(rows,indent=2)+'\n')
for row in rows: print(json.dumps(row))
