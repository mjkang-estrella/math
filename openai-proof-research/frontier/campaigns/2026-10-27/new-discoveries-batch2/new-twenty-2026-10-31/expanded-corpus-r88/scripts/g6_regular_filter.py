# Stream a gzipped graph6 file and keep regular graphs (degree test only). Args: in.gz out start_line count
import sys, gzip
src,dst,start,count=sys.argv[1],sys.argv[2],int(sys.argv[3]),int(sys.argv[4])
out=open(dst,'a'); kept=0; seen=0
with gzip.open(src,'rb') as f:
    for idx,line in enumerate(f):
        if idx<start: continue
        if idx>=start+count: break
        seen+=1
        s=line.strip(); data=[c-63 for c in s]; n=data[0]
        deg=[0]*n; t=0; bitpos=0
        bits=[]
        for x in data[1:]:
            bits.extend(((x>>5)&1,(x>>4)&1,(x>>3)&1,(x>>2)&1,(x>>1)&1,x&1))
        for j in range(1,n):
            for i in range(j):
                if bits[t]: deg[i]+=1; deg[j]+=1
                t+=1
        if min(deg)==max(deg): out.write(s.decode()+'\n'); kept+=1
print(start,seen,kept)
