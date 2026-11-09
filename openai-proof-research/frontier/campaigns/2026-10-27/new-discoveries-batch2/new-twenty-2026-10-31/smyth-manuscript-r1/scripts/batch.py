import runpy,sys
from pathlib import Path
sys.setrecursionlimit(20000)
a=runpy.run_path(str(Path(__file__).with_name('audit.py')))
if sys.argv[1]=='family':
 for b in range(int(sys.argv[2]),int(sys.argv[3])+1):a['family'](b)
else:
 A=int(sys.argv[2])
 for B in range(2,A):a['sweep'](A,B)
