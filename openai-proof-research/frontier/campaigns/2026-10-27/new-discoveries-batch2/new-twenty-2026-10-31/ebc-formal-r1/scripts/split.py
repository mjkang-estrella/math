from pathlib import Path
L=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/ebc-formal-r1')
s=(L/'src/Arithmetic.lean').read_text()
base,rest=s.split('theorem rational_row_1_0',1)
(L/'src/ArithmeticBase.lean').write_text(base+'end EBC337062\n')
rest='theorem rational_row_1_0'+rest
rows=[line for line in rest.splitlines() if line.startswith('theorem rational_row_')]
modules=[]
for i in range(8):
 name=f'Rows{i}';modules.append(name)
 (L/f'src/{name}.lean').write_text('import ArithmeticBase\nnamespace EBC337062\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'+'\n'.join(rows[i*8:(i+1)*8])+'\nend EBC337062\n')
lines=rest.splitlines();out=[];skip=False
for line in lines:
 if line.startswith('theorem rational_row_'):continue
 out.append(line)
(L/'src/Arithmetic.lean').write_text('\n'.join('import '+m for m in modules)+'\nnamespace EBC337062\n'+'\n'.join(out)+'\n')
(L/'module-order.txt').write_text('\n'.join(['Definitions','Control','ArithmeticBase']+modules+['Arithmetic','Endpoint','Audit'])+'\n')
