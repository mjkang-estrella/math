"""Read-only Git object decoder. No git commands, writes, or repository operations."""
import zlib,struct,hashlib
class Objects:
 def __init__(self,g):
  self.g=g;self.cache={};self.packs=[]
  for p in (g/'objects/pack').glob('*.idx'):
   d=p.read_bytes();assert d[:8]==b'\xfftOc\x00\x00\x00\x02';n=struct.unpack('!I',d[1028:1032])[0]
   ids=[d[1032+20*i:1052+20*i].hex() for i in range(n)];start=1032+24*n
   offs=struct.unpack('!'+str(n)+'I',d[start:start+4*n]);large=start+4*n
   offsets={oid:(struct.unpack('!Q',d[large+8*(off&0x7fffffff):large+8*(off&0x7fffffff)+8])[0] if off&0x80000000 else off) for oid,off in zip(ids,offs)}
   self.packs.append((p.with_suffix('.pack'),offsets))
 def get(self,oid):
  if oid in self.cache:return self.cache[oid]
  p=self.g/'objects'/oid[:2]/oid[2:]
  if p.exists():
   raw=zlib.decompress(p.read_bytes());hdr,data=raw.split(b'\0',1);kind=hdr.split()[0].decode()
  else:
   pack,offset=next((p,o[oid]) for p,o in self.packs if oid in o)
   kind,data=self.at(pack,offset)
  assert hashlib.sha1(kind.encode()+b' '+str(len(data)).encode()+b'\0'+data).hexdigest()==oid
  self.cache[oid]=(kind,data);return kind,data
 def at(self,p,offset):
  with p.open('rb') as f:
   f.seek(offset);c=f.read(1)[0];typ=(c>>4)&7
   while c&128:c=f.read(1)[0]
   base=None
   if typ==6:
    c=f.read(1)[0];dist=c&127
    while c&128:c=f.read(1)[0];dist=((dist+1)<<7)+(c&127)
    base=self.at(p,offset-dist)
   elif typ==7:base=self.get(f.read(20).hex())
   de=zlib.decompressobj();data=b''
   while not de.eof:data+=de.decompress(f.read(65536))
  if base is None:return {1:'commit',2:'tree',3:'blob',4:'tag'}[typ],data
  kind,old=base;i=0
  def varint():
   nonlocal i
   n=shift=0
   while True:
    b=data[i];i+=1;n|=(b&127)<<shift;shift+=7
    if not b&128:return n
  assert varint()==len(old);size=varint();out=bytearray()
  while i<len(data):
   c=data[i];i+=1
   if c&128:
    off=n=0
    for j in range(4):
     if c&(1<<j):off|=data[i]<<(8*j);i+=1
    for j in range(3):
     if c&(16<<j):n|=data[i]<<(8*j);i+=1
    out.extend(old[off:off+(n or 65536)])
   else:assert c;out.extend(data[i:i+c]);i+=c
  assert len(out)==size;return kind,bytes(out)
 def tree(self,rev):
  kind,data=self.get(rev);assert kind=='commit';oid=data.splitlines()[0].split()[1].decode();result={}
  def walk(oid,prefix):
   kind,d=self.get(oid);assert kind=='tree';i=0
   while i<len(d):
    end=d.index(b'\0',i);mode,name=d[i:end].split(b' ',1);oid=d[end+1:end+21].hex();i=end+21;path=prefix+name.decode()
    if mode==b'40000':walk(oid,path+'/')
    elif mode!=b'160000':result[path]=oid
  walk(oid,'');return result
