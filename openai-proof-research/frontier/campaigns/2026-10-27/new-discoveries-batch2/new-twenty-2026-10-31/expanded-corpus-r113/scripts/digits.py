import time,json
x=0;ones=0;T=time.monotonic()
for k in range(1,2**21+1):
 a=1 if x&1 else 2;ones+=a==1;x=(x+(x<<1)+a)>>1
 if k in [200,2**16,2**18,2**20,2**21]:print(json.dumps({'k':k,'ones':ones,'twos':k-ones,'sat_bits':x.bit_length(),'seconds':time.monotonic()-T}),flush=True)
