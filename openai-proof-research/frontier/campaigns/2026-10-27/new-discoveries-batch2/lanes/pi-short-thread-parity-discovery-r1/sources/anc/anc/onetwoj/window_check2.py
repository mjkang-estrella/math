# independent (verify/fam) check of the closed formula on z in [y-3, y+8] for even y up to YMAX
import subprocess,sys
from lemmas import gform
YMAX=int(sys.argv[1]); bad=0; cnt=0
for y in range(6,YMAX+1,2):
    Z=y+8
    g=[None]+list(map(int,subprocess.run(['../raw_cpp/fam','1',str(y),str(Z)],capture_output=True,text=True).stdout.split()))
    for z in range(y-2,Z+1):
        cnt+=1
        if g[z]!=gform(y,z): bad+=1; print('bad',y,z)
    if g[y-3]==gform(y,y-3): print('formula also holds at y-3 for y=',y)
print('checked',cnt,'bad',bad)
