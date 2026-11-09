from generate_reduced import *
rr=json.loads((L/'frozen/frozen/inputs/compression/verification.json').read_text())['receipts'];done=set((L/'completed-modules.txt').read_text().splitlines())|{'C10_8_1Case','C10_10_1Case'}
mods=[];cases=[]
for r in sorted(rr,key=lambda r:(r['groups'],r['vertices'])):
 if r['verified']!='potential-inequalities':continue
 a,b,e=(r[t] for t in ['a','b','e'])
 if f'C{a}_{b}_{e}Case' in done:continue
 mm=generate(a,b,e);mods+=mm;cases.append([a,b,e])
(L/'reduced-plan.txt').write_text('\n'.join(mods)+'\n');(L/'reduced-cases.json').write_text(json.dumps(cases))
print(cases,len(mods))
