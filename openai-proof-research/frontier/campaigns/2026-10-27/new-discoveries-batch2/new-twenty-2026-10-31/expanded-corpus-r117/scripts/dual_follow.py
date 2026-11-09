import json,pathlib,collections
D=pathlib.Path(__file__).resolve().parents[1];sets=json.loads((D/'outputs/dual-survivors.json').read_text());out=[]
def add(a,b):return (a%8+b%8)%8+8*((a//8+b//8)%8)
def sub(a,b):return (a%8-b%8)%8+8*((a//8-b//8)%8)
for S in sets:
 S=set(S);periods=[h for h in range(1,64) if {add(x,h) for x in S}==S]
 nu=collections.Counter(sub(a,b) for a in S for b in S)
 gal=all(nu[h]==nu[(h%8*3%8)+8*(h//8*3%8)]==nu[(h%8*5%8)+8*(h//8*5%8)] for h in range(64))
 out.append({'S':sorted(S),'periods':periods,'galois_difference':gal})
(D/'outputs/dual-follow.json').write_text(json.dumps(out,indent=2))
print('survivors',len(out),'periodic',sum(bool(x['periods']) for x in out),'galois',sum(x['galois_difference'] for x in out),'aperiodic',sum(not x['periods'] for x in out))
print('aperiodic examples', [x for x in out if not x['periods']][:3])
