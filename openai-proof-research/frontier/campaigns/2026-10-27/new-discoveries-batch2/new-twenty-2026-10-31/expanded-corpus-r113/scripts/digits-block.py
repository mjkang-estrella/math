import pathlib,json,time
D=pathlib.Path(__file__).resolve().parents[1];cp=D/'outputs/digit-checkpoint.json';T=time.monotonic()
if cp.exists():
 o=json.loads(cp.read_text());x=int(o['sat_hex'],16);k=o['k'];ones=o['ones']
else:x=0;k=0;ones=0
while k<2**21:
 end=min(k+2**17,2**21)
 while k<end:
  a=1 if x&1 else 2;ones+=a==1;x=(x+(x<<1)+a)>>1;k+=1
 cp.write_text(json.dumps({'sat_hex':hex(x),'k':k,'ones':ones}))
 print(json.dumps({'k':k,'ones':ones,'twos':k-ones,'seconds':time.monotonic()-T}),flush=True)
 if time.monotonic()-T>75:break
