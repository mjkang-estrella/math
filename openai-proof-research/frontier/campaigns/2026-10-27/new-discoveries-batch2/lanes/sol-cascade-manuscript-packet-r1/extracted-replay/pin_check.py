"""Read-only filesystem verification; no git commands or repository writes."""
from pathlib import Path
import hashlib,struct,zlib,json,subprocess

def obj(kind,data):return hashlib.sha1(kind.encode()+b' '+str(len(data)).encode()+b'\0'+data).digest()
def commit_bytes(g,rev):
 loose=g/'objects'/rev[:2]/rev[2:]
 if loose.exists():return zlib.decompress(loose.read_bytes()).split(b'\0',1)[1]
 for idx in (g/'objects/pack').glob('*.idx'):
  d=idx.read_bytes();assert d[:8]==b'\xfftOc\0\0\0\2';n=struct.unpack('>I',d[1028:1032])[0];names=d[1032:1032+20*n];needle=bytes.fromhex(rev)
  lo=0;hi=n
  while lo<hi:
   mid=(lo+hi)//2
   if names[20*mid:20*mid+20]<needle:lo=mid+1
   else:hi=mid
  if names[20*lo:20*lo+20]!=needle:continue
  off=struct.unpack_from('>I',d,1032+24*n+4*lo)[0]
  if off&0x80000000:off=struct.unpack_from('>Q',d,1032+28*n+8*(off&0x7fffffff))[0]
  with idx.with_suffix('.pack').open('rb') as f:
   f.seek(off);v=f.read(1)[0];typ=(v>>4)&7
   while v&128:v=f.read(1)[0]
   assert typ==1,('commit delta unsupported',rev,typ)
   dec=zlib.decompressobj();out=b''
   while not dec.eof:out+=dec.decompress(f.read(65536))
   return out
 raise AssertionError(rev)
def check(b):
 pins=json.loads((b/'pins.json').read_text());lean=Path(pins['lean_binary'])
 assert hashlib.sha256(lean.read_bytes()).hexdigest()==pins['lean_sha256']=='e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550'
 assert subprocess.check_output([str(lean),'--version'],text=True).strip()==pins['lean_version']
 result={}
 for name,e in pins['packages'].items():
  p=Path(e['path']);g=p/'.git';head=(g/'HEAD').read_text().strip()
  if head.startswith('ref: '):
   ref=head[5:];rp=g/ref
   head=rp.read_text().strip() if rp.exists() else next(s.split()[0] for s in (g/'packed-refs').read_text().splitlines() if s.endswith(' '+ref))
  assert head==e['revision'],(name,head)
  tree=commit_bytes(g,head).splitlines()[0].decode().split()[1]
  d=(g/'index').read_bytes();assert d[:4]==b'DIRC';version,n=struct.unpack_from('>II',d,4);assert version==2,version
  pos=12;root={};hashes={}
  for _ in range(n):
   start=pos;mode=struct.unpack_from('>I',d,pos+24)[0];digest=d[pos+40:pos+60];flags=struct.unpack_from('>H',d,pos+60)[0];assert not flags&0x3000
   end=d.index(b'\0',pos+62);path=d[pos+62:end].decode();pos=start+((end+1-start+7)//8)*8
   f=p/path;data=f.read_bytes() if mode!=0o120000 else str(f.readlink()).encode();assert obj('blob',data)==digest,(name,path,'dirty')
   hashes[path]=hashlib.sha256(data).hexdigest();t=root
   parts=path.split('/')
   for part in parts[:-1]:t=t.setdefault(part,{})
   t[parts[-1]]=(mode,digest)
  def treehash(t):
   data=b''
   for k,v in sorted(t.items(),key=lambda kv:(kv[0]+('/' if isinstance(kv[1],dict) else '')).encode()):
    mode,h=(0o40000,treehash(v)) if isinstance(v,dict) else v
    data+=oct(mode)[2:].encode()+b' '+k.encode()+b'\0'+h
   return obj('tree',data)
  assert treehash(root).hex()==tree,(name,'index not committed tree')
  # All untracked .lean inputs under the package source tree would undermine the pin.
  extra=[str(f.relative_to(p)) for f in p.rglob('*.lean') if '.git' not in f.parts and '.lake' not in f.relative_to(p).parts and str(f.relative_to(p)) not in hashes]
  assert not extra,(name,extra)
  result[name]={'revision':head,'tree':tree,'tracked_files':len(hashes),'tracked_sha256':hashes}
 return result
if __name__=='__main__':
 b=Path(__file__).resolve().parent;(b/'package-audit.json').write_text(json.dumps(check(b),indent=2,sort_keys=True)+'\n');print('all eight pins and clean tracked source trees PASS')
