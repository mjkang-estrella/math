"""Preparation only: exact bounded readings and HTML text representation."""
from pathlib import Path
import json,hashlib,sys
S=Path('frontier/sources/i124_fractal_incidence_discovery')
def record(path,start=1,end=None,convention='splitlines',scope='selected passage'):
 p=Path(path);b=p.read_bytes();ls=b.decode().splitlines() if convention=='splitlines' else b.decode().split('\n');end=end or len(ls)
 assert 1<=start<=end<=len(ls)
 chunk='\n'.join(ls[start-1:end]);h=lambda x:hashlib.sha256(x).hexdigest()
 obj=dict(local=str(p),start=start,end=end,convention=convention,line_count=len(ls),file_sha256=h(b),passage_sha256=h(chunk.encode()),scope=scope)
 mf=S/'read-manifest.json';d=json.loads(mf.read_text()) if mf.exists() else {'passages':[]}
 if obj not in d['passages']:d['passages'].append(obj);mf.write_text(json.dumps(d,indent=2)+'\n')
 print('FILE',str(p),start,end);print(chunk)
if __name__=='__main__':record(sys.argv[1],int(sys.argv[2]) if len(sys.argv)>2 else 1,int(sys.argv[3]) if len(sys.argv)>3 else None)
