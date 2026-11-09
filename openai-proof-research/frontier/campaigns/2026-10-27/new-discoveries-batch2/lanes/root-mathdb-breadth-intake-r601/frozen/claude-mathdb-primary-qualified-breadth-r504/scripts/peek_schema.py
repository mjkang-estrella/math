import json,sys
p=sys.argv[1]
d=json.load(open(p,encoding='utf-8'))
def sh(x,depth=0):
    if isinstance(x,dict):
        return {k:(sh(v,depth+1) if depth<1 else type(v).__name__) for k,v in list(x.items())[:12]}
    if isinstance(x,list):
        return ['list[%d]'%len(x), sh(x[0],depth+1) if x else None]
    return type(x).__name__
print(json.dumps(sh(d),indent=1)[:3000])
