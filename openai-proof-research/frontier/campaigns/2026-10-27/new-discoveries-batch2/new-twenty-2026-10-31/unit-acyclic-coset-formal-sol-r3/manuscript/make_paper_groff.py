from pathlib import Path
import ast,subprocess
lane=Path(__file__).resolve().parent.parent
out=lane/'manuscript'
tree=ast.parse((out/'make_paper.py').read_text())
ms=['.nr PO 0.7i','.nr LL 6.8i','.nr PS 11','.nr VS 15','.nr HM 0.65i','.nr FM 0.6i','.ds LH INTERNAL DRAFT - 340110','.ds RH Independent review pending','.ds LF Credit 0 - campaign 55/60','.ds RF Page %','.TL','A periodic-coset obstruction to unit acyclic matchings','.AU','Internal research draft']
plain=[]
for n in tree.body:
    if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call) and isinstance(n.value.func,ast.Name):
        call=n.value;name=call.func.id
        if name in ('p','h'):
            text=ast.literal_eval(call.args[0]);plain.append(text)
            ms.extend(['.PP' if name=='p' else '.NH 2',text.replace('\\','\\e')])
        elif name=='page':ms.append('.bp')
(out/'340110.ms').write_text('\n'.join(ms)+'\n')
(out/'340110-draft.txt').write_text('\n\n'.join(plain))
with (out/'340110.ps').open('wb') as f:
    subprocess.run(['groff','-Tps','-ms',str(out/'340110.ms')],stdout=f,check=True)
subprocess.run(['gs','-dBATCH','-dNOPAUSE','-dSAFER','-sDEVICE=pdfwrite','-sOutputFile='+str(out/'340110-draft.pdf'),str(out/'340110.ps')],check=True)
