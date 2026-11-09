import periodic, sys, time
X=int(sys.argv[1]); Y=int(sys.argv[2]); R=int(sys.argv[3])
for x in range(X, X+1):
    for y in range(x, Y+1):
        t=time.time()
        S=periodic.Spider(x,y); S.compute(R)
        seq=[S.G(z) for z in range(1,R+1)]
        tail=seq[R//2:]
        per=None
        for q in range(1,65):
            if all(tail[k]==tail[k+q] for k in range(len(tail)-q)): per=q;break
        if per is None:
            print("(%d,%d): no period<=64 in tail; max=%d"%(x,y,max(seq)),flush=True); continue
        start=R//2+1
        while start-1>=1 and seq[start-2]==seq[start-2+per]: start-=1
        pat=seq[start-1:start-1+per]
        cls=''.join('P' if seq[z-1]==(x+y+z)%2 else ('A' if seq[z-1]==1-(x+y+z)%2 else 'X') for z in range(start,start+per))
        zm2 = all(seq[z-1]==z%2 for z in range(start,R+1))
        print("(%d,%d): period %d from z=%d pattern %s class %s  G=z mod 2 eventually: %s  max=%d  [%.0fs]"%(x,y,per,start,''.join(map(str,pat)),cls,zm2,max(seq),time.time()-t),flush=True)
