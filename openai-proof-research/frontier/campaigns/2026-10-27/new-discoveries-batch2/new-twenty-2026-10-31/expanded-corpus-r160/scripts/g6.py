def g6decode(s):
    s=s.strip(); d=[ord(c)-63 for c in s]
    n=d[0]; bits=[]
    for x in d[1:]:
        for k in range(5,-1,-1): bits.append((x>>k)&1)
    adj=[0]*n; t=0
    for j in range(1,n):
        for i in range(j):
            if bits[t]: adj[i]|=1<<j; adj[j]|=1<<i
            t+=1
    return n,adj
