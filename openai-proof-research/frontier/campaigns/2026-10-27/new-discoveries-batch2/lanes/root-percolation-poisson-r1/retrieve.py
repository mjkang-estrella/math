from pathlib import Path
import urllib.request, json, hashlib, datetime, concurrent.futures, re

B = Path(__file__).resolve().parent
O = B/'sources'
O.mkdir(exist_ok=True)
records=[]
def get(name,url):
    rec={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Public mathematical research'}),timeout=35) as r:
            data=r.read();rec['status']=r.status
        if name.endswith('.pdf'): assert data.startswith(b'%PDF')
        (O/name).write_bytes(data)
        rec.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
        result=json.loads(data) if name.endswith('.json') else data
    except Exception as e:
        rec['error']=str(e); result=None
    records.append(rec)
    return result

if __name__=='__main__':
    with concurrent.futures.ThreadPoolExecutor(4) as ex:
        jobs=[ex.submit(get,n,u) for n,u in [
            ('source.html','https://arxiv.org/html/2408.08457v2'),
            ('source.pdf','https://arxiv.org/pdf/2408.08457v2'),
            ('source-abs.html','https://arxiv.org/abs/2408.08457'),
            ('author.html','https://www.math.ucla.edu/~gladkovna/')]]
        for j in jobs:j.result()
    hits={}
    for label,repo,dirs in [('omega','the-omega-institute/trureturing',['Problems','D5','Blueprint']),('openai','openai/math',['preprints'])]:
        h=get(label+'-head.json',f'https://api.github.com/repos/{repo}/commits/HEAD')
        if not h:continue
        print(label,h['sha'],h['commit']['committer']['date'],flush=True)
        root=get(label+'-root.json',f'https://api.github.com/repos/{repo}/git/trees/{h["sha"]}')
        for dn in dirs:
            ent=next(x for x in root['tree'] if x['path']==dn)
            tree=get(label+'-'+dn+'-tree.json',f'https://api.github.com/repos/{repo}/git/trees/{ent["sha"]}?recursive=1')
            assert tree and not tree['truncated']
            found=[x for x in tree['tree'] if x['type']=='blob' and re.search(r'364374|2408.?08457|gladkov|poisson|percolation|disjoint.?path|log.?concav|network.?flow',x['path'],re.I)]
            hits[label+'/'+dn]=found
            print(dn,len(tree['tree']),len(found),'hits',flush=True)
        get(label+'-readme.md',f'https://raw.githubusercontent.com/{repo}/{h["sha"]}/'+('CONTENTS.md' if label=='openai' else 'README.md'))
    (B/'retrieval.json').write_text(json.dumps(records,indent=2)+'\n')
    (B/'registry-hits.json').write_text(json.dumps(hits,indent=2)+'\n')
    for k,v in hits.items():
        for x in v:print(k,x['path'])
