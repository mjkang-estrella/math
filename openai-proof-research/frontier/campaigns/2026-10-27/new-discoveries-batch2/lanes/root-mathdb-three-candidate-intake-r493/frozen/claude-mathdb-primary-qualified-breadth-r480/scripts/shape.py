import json,sys
def sh(x,d=0,maxd=3):
    if d>maxd: return '...'
    if isinstance(x,dict): return {k:sh(v,d+1,maxd) for k,v in list(x.items())[:25]}
    if isinstance(x,list): return [len(x), sh(x[0],d+1,maxd)] if x else []
    return type(x).__name__ if not isinstance(x,(int,float)) or True else x
for p in sys.argv[1:]:
    print(p); print(json.dumps(sh(json.load(open(p))),indent=1)[:3000])
