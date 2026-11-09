from pathlib import Path
import json,re
D=Path(__file__).resolve().parents[1];s=(D/'formal/Riordan.lean').read_text();core=s.split('def A :')[0];(D/'formal/Core.lean').write_text(core+'end Riordan\n')
o=json.loads((D/'outputs/riordan-witness.json').read_text());names=', '.join(re.findall(r'theorem (pc_\d+_\d+)',core))
for i,row in enumerate(o['A']):
 vals='!['+','.join(map(str,row))+']'
 txt=f'import Core\nnamespace Riordan\ntheorem row{i} : ∀ j : Fin 15, entry {i} j = ({vals} : Fin 15 → ℕ) j := by\n  intro j\n  fin_cases j <;> norm_num [entry, {names}]\nend Riordan\n'
 (D/f'formal/Row{i}.lean').write_text(txt)
final='\n'.join(f'import Row{i}' for i in range(15))+'\nnamespace Riordan\n'+s.split('def A :',1)[1];final='\n'.join(f'import Row{i}' for i in range(15))+'\nnamespace Riordan\ndef A :'+s.split('def A :',1)[1]
start=final.index(' := by\n  intro i j',final.index('theorem entries'))
end=final.index('\ntheorem kernel',start)
final=final[:start]+''' := by
  intro i
  fin_cases i
'''+''.join(f'  · exact row{i}\n' for i in range(15))+final[end:]
# Use table rows for finite io checks instead of repeating polynomial arithmetic.
for key in ['even_independent','odd_copy']:
 a=final.index(' := by',final.index('theorem '+key));b=final.index('\n',final.index('norm_num [entry,',a));line=final[a:b];line=re.sub(r'norm_num \[entry, .*\]', 'norm_num [entries]',line);final=final[:a]+line+final[b:]
(D/'formal/Endpoint.lean').write_text(final)
