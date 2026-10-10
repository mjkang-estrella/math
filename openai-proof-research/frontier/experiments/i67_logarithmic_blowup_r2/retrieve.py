"""One-time bounded official retrieval; writes only the I67 source directory."""
from pathlib import Path
import concurrent.futures, datetime, hashlib, json, urllib.request, urllib.error

ROOT = Path(__file__).resolve().parents[3]
OUT = ROOT / 'frontier/sources/i67_logarithmic_blowup_r2/primary'
OLD = ROOT / 'frontier/sources/i66_dispersive_equation_discovery'

def main():
    OUT.mkdir(parents=True, exist_ok=True)
    requests = []
    for name, ident, version in [('buck','2609.23685',1),('li','2304.02078',2),
                                 ('cao','2410.04532',1),('wallauch','2006.04600',1),
                                 ('du','1805.02775',3)]:
        requests += [(name+'-abs', 'https://arxiv.org/abs/'+ident),
                     (name+'-proof','https://arxiv.org/html/'+ident+'v'+str(version))]
    pins = json.loads((OLD/'pinned-manifest.json').read_text())
    for section in ['profiles','linear','nonlinear']:
        x = next(x for x in pins if 'Stable-' in x['path'] and x['path'].endswith('/'+section+'.tex'))
        requests.append(('pin-'+section,x['url']))
    def fetch(item):
        name,url=item
        r={'name':name,'url':url,'retrieved_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
        try:
            with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'I67 original-proof audit'}),timeout=25) as f:
                data=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
        except urllib.error.HTTPError as e:
            data=e.read();r.update(status=e.code,error=str(e),headers=dict(e.headers))
        except Exception as e:
            data=str(e).encode();r.update(status=None,error=str(e))
        path=OUT/(name+'.raw');path.write_bytes(data)
        r.update(path=str(path.relative_to(ROOT)),bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
        return r
    with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:
        results=list(ex.map(fetch,requests))
    (OUT/'responses.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps([{k:x.get(k) for k in ['name','status','error']} for x in results],indent=2))

if __name__=='__main__':main()
