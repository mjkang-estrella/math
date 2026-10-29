import urllib.request, urllib.error, json, hashlib, datetime
from pathlib import Path
D=Path(__file__).parent
out=[]
def get(url,name):
    r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'independent-math-review'}),timeout=25) as f:
            data=f.read();r.update(status=f.status,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
            (D/name).write_bytes(data)
            value=json.loads(data) if name.endswith('.json') else data.decode()
    except Exception as e:r['error']=str(e);value=None
    out.append(r)
    (D/'http-evidence.json').write_text(json.dumps(out,indent=2))
    return value
for short,repo,old in [('omega','the-omega-institute/trureturing','28414a3d55d5b97458b138701407d5678e167a8e'),('openai','openai/math','7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a')]:
    h=get('https://api.github.com/repos/'+repo+'/commits/HEAD',short+'-head.json')
    if h and h['sha']!=old:
        delta=get('https://api.github.com/repos/'+repo+'/compare/'+old+'...'+h['sha'],short+'-delta.json')
        if delta:
            for k,f in enumerate(delta.get('files',[])):
                if f['filename'].endswith('.md') and f['status']!='removed':
                    get('https://raw.githubusercontent.com/'+repo+'/'+h['sha']+'/'+f['filename'],short+'-changed-'+str(k)+'.md')
print(json.dumps(out,indent=2))
