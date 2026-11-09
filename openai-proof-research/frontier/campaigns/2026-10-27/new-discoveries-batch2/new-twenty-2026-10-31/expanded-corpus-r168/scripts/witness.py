import pathlib,json,itertools
D=pathlib.Path(__file__).resolve().parents[1];ms=json.loads((D/'outputs/matchdeep.json').read_text())[-1]['COUNTEREXAMPLE'];es=[(a,b,c) for c,m in enumerate(ms) for a,b in m];spectrum={};count=0
for choices in itertools.product(range(8),itertools.combinations(range(8),3),itertools.combinations(range(8),3)):
 sel=[es[choices[0]]]+[es[8+i] for i in choices[1]]+[es[16+i] for i in choices[2]];vertices=[v for a,b,c in sel for v in (a,b)];count+=1
 assert len(set(vertices))<14,choices
local=[e for e in es if e[0]<8];matches=[]
for mask in range(1<<12):
 sel=[e for i,e in enumerate(local) if mask>>i&1];vertices=[v for a,b,c in sel for v in (a,b)]
 if len(set(vertices))!=len(vertices):continue
 tr=tuple(sum(c==j for a,b,c in sel) for j in range(3));spectrum[tr]=spectrum.get(tr,0)+1;matches.append(mask)
r={'source':'Conjecture 1.3 arXiv2212.03100v2','n':8,'counts':[1,3,3],'independent_combination_checks':count,'local_edges':local,'local_spectrum':[{'counts':t,'multiplicity':c} for t,c in sorted(spectrum.items())],'all_local_matching_masks':matches,'components':[list(range(8)),list(range(8,16))]};(D/'outputs/witness-independent.json').write_text(json.dumps(r,indent=2));print(r['local_spectrum'])
