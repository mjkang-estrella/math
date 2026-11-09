import sys,time,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import get
todo=[a.split('=',1) for a in sys.argv[1:]]
for k,u in todo: get(k,u); time.sleep(2)
