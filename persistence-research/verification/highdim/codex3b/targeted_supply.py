"""Report useful period alignments for each adic signature; search-only data."""
import sys
sys.dont_write_bytecode=True
import json,math,pathlib,collections
HERE=pathlib.Path(__file__).resolve().parent
s=json.load(open(HERE/'supply_extended.json'))
periods=collections.defaultdict(list)
for p,d,a,w in s:
 if d>2000:continue
 periods[d].append({'p':p,'uu_index':(p-1)//math.lcm(a,w),'a_index':(p-1)//a,'w_index':(p-1)//w})
out={str(d):v for d,v in sorted(periods.items()) if any(max(e['uu_index'],e['a_index'],e['w_index'])>=4 for e in v)}
json.dump(out,open(HERE/'period_strengths.json','w'),indent=1)
for d in (3,8,9,12,16,18,20,21,22,24,27,30,32,36,40,42,45,63,66,81,108,121):
 vals=periods[d]
 print(d,sorted(vals,key=lambda e:-max(e['uu_index'],e['a_index'],e['w_index']))[:3])
