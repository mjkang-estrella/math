from generate_cases import *
records=json.loads((L/'frozen/frozen/inputs/compression/verification.json').read_text())['receipts']
records=sorted([r for r in records if r['verified']=='potential-inequalities' and (r['a'],r['b'],r['e']) not in [(10,10,1),(10,8,1)]],key=lambda r:(r['groups'],r['vertices']))
mods=[]
for r in records:mods+=generate(r['a'],r['b'],r['e'])
(L/'serial-plan.txt').write_text('\n'.join(mods)+'\n')
