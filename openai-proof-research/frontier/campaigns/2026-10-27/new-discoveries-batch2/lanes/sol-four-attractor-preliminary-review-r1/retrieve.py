from pathlib import Path
import urllib.request, urllib.error, hashlib, json, datetime
D=Path(__file__).parent
def fetch(url,name):
    rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalSourceReview/1.0'}),timeout=35) as r:
            data=r.read(12_000_001); rec.update(status=r.status,final_url=r.url)
        assert len(data)<=12_000_000
        p=D/'retrieved'/name;p.parent.mkdir(exist_ok=True);p.write_bytes(data)
        rec.update(file=str(p.relative_to(D)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
        q=D/'retrieved'/(name+'.frozen');q.write_bytes(data)
        assert p.read_bytes()==q.read_bytes()
    except Exception as e:rec.update(error=repr(e))
    with (D/'access.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
    print(json.dumps(rec))
if __name__=='__main__':
    import sys
    fetch(sys.argv[1],sys.argv[2])
