import json,pathlib,collections
D=pathlib.Path(__file__).resolve().parents[1];ss=json.loads((D/'outputs/dual-survivors.json').read_text());U={tuple(sorted(s)) for s in ss}
def sub(a,b):return (a%8-b%8)%8+8*((a//8-b//8)%8)
def norm(S,o,a,b):
 a=sub(a,o);b=sub(b,o);det=(a%8*(b//8)-(a//8)*(b%8))%8
 if det%2==0:return None
 inv=pow(det,-1,8)
 return tuple(sorted(((b//8*(v%8)-b%8*(v//8))*inv%8)+8*((-(a//8)*(v%8)+a%8*(v//8))*inv%8) for v in [sub(x,o) for x in S]))
out=[]
while U:
 S=min(U);orb={norm(S,o,a,b) for o in S for a in S for b in S};orb.discard(None);assert orb<=U
 out.append({'representative':S,'normalized_orbit_size':len(orb)});U-=orb
print(json.dumps(out));(D/'outputs/dual-orbits.json').write_text(json.dumps(out,indent=2))
