from pathlib import Path
import json,collections,re
r=Path(__file__).resolve().parents[1];rs=json.loads((r/'new-certificates.json').read_text());ss=json.loads((r/'new-supports.json').read_text())
def lit(a):return '!!['+'; '.join(', '.join(map(str,row)) for row in a)+']'
for sp in ss:
 f=r/'formal'/f'FiniteSupport{sp["index"]:03}.lean';s=f.read_text();groups=collections.OrderedDict()
 for n in sp['ids']:
  a=rs[n]['matrix'];key=tuple(abs(x) for row in a for x in row);groups.setdefault(key,[]).append(n)
 lines=[]
 for k,(key,ids) in enumerate(groups.items()):
  a=[[0]*8 for _ in range(8)]
  for i in range(8):
   for j in range(8):a[sp['order'][i]][sp['order'][j]]=key[8*i+j]
  lines.append(f'def U{k} : QuotientMatrix := {lit(a)}')
 lines += [f'theorem unsigned_enumeration : unsignedPatterns {sp["code"]} = {{{", ".join("U"+str(k) for k in range(len(groups)))}}} := by','  decide +kernel']
 for k,ids in enumerate(groups.values()):
  refs=[f'NewCertificates{n//32:04}.C{n}' for n in ids]
  lines += [f'theorem signed_enumeration{k} : signedPatterns (U{k}.submatrix e e) p = {{{", ".join(refs)}}} := by','  decide +kernel']
 lines += [f'theorem enumeration : signedCatalogue {sp["code"]} e p = matrices := by','  simp only [signedCatalogue, unsigned_enumeration, Finset.biUnion_insert, Finset.singleton_biUnion, '+', '.join(f'signed_enumeration{k}' for k in range(len(groups)))+', Finset.insert_union, Finset.singleton_union, matrices]']
 s=re.sub(r'theorem enumeration :.*?\n  decide \+kernel\n','\n'.join(lines)+'\n',s,flags=re.S)
 f.write_text(s)
print('Split all support enumeration proofs by unsigned pattern')
