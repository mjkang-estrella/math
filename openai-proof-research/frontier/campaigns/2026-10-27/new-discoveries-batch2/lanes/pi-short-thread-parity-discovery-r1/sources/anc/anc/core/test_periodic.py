import periodic, time
ref={}
for line in open('sp3_120.txt'):
    x,y,z,g=map(int,line.split()); ref[(x,y,z)]=g
def refG(x,y,z):
    return ref[tuple(sorted((x,y,z)))]
bad=0
t=time.time()
for x in range(1,7):
    for y in range(x,9):
        S=periodic.Spider(x,y); S.compute(120)
        for z in range(1,121):
            if S.G(z)!=refG(x,y,z): bad+=1; print("MISMATCH",x,y,z,S.G(z),refG(x,y,z))
print("mismatches",bad,"time",time.time()-t)
