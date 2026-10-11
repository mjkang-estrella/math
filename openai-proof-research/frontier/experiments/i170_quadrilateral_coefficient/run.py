import sys,json,importlib.util
from pathlib import Path
base=Path(__file__).resolve().parent
root=base.parents[2]
def mod(name):
    spec=importlib.util.spec_from_file_location(name,base/(name+'.py'));m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
C=mod('core');M=mod(sys.argv[1]);print(json.dumps(M.run(C,root),sort_keys=True,indent=2))
