import gzip
def parse(s):
    s=s.strip()
    n=ord(s[0])-63; bits=[]
    for ch in s[1:]:
        v=ord(ch)-63
        for k in range(5,-1,-1): bits.append((v>>k)&1)
    adj=[0]*n; idx=0
    for j in range(1,n):
        for i in range(j):
            if bits[idx]: adj[i]|=1<<j; adj[j]|=1<<i
            idx+=1
    return n,adj
def stream(path,start=0,count=None):
    op=gzip.open if path.endswith('.gz') else open
    with op(path,'rt') as f:
        for k,line in enumerate(f):
            if k<start: continue
            if count is not None and k>=start+count: break
            yield k,line
