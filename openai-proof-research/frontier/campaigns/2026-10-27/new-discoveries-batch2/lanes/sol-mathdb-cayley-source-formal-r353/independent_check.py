from pathlib import Path
import runpy,json
L=Path(__file__).resolve().parent
p=L.parent/'root-mathdb-cayley-review-intake-r336/frozen/scripts/independent_cayley_check.py'
f=runpy.run_path(str(p))
ws=list(f['packed_words'](5));assert len(ws)==541
r={'total':len(ws),'counts':{}}
for pat,expected in [((1,1,2,2),520),((1,1,1,2),522)]:
 for w in ws:assert f['contains_norm'](w,pat)==f['contains_pairwise'](w,pat)
 v=sum(not f['contains_pairwise'](w,pat) for w in ws);assert v==expected
 r['counts'][''.join(map(str,pat))]={'avoiding':v,'containing':len(ws)-v}
assert f['count_avoiding'](ws,(1,1,2))==360
assert f['count_avoiding'](ws,(1,2,2))==360
(L/'independent-check.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))
