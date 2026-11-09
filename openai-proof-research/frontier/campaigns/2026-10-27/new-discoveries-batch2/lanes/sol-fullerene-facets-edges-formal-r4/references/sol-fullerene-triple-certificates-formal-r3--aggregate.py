from pathlib import Path
import json
L=Path(__file__).resolve().parent
C=json.loads((L/'coverage.json').read_text())
def combine(items,sep):
 if len(items)==1:return items[0]
 h=len(items)//2
 return '('+combine(items[:h],sep)+sep+combine(items[h:],sep)+')'
def proof(items):
 if len(items)==1:return items[0]
 h=len(items)//2
 return '(mergeChecked '+proof(items[:h])+' '+proof(items[h:])+')'
for tag in ['G','H']:
 mods=C[tag]['modules'];groups=[]
 for h in range(0,len(mods),16):
  subset=mods[h:h+16];name=f'Group{tag}{h//16:02d}';groups.append(name)
  ids=[f'{tag}{n:03d}' for n in range(h,min(h+16,len(mods)))]
  t=['import '+m for m in subset]+['namespace TripleCertificates',f'noncomputable def records{name} : List Certificate := '+combine(['records'+n for n in ids],' ++ '),f'theorem checked{name} : ∀ r ∈ records{name}, checked A{tag} D{tag} P{tag} r := '+proof(['checked'+n for n in ids]),'end TripleCertificates']
  (L/f'{name}.lean').write_text('\n'.join(t)+'\n')
 name=f'All{tag}'
 t=['import '+m for m in groups]+['import Domain','set_option maxRecDepth 20000','set_option maxHeartbeats 2000000','namespace TripleCertificates',f'noncomputable def records{tag} : List Certificate := '+combine(['records'+n for n in groups],' ++ '),f'theorem checked{tag} : ∀ r ∈ records{tag}, checked A{tag} D{tag} P{tag} r := '+proof(['checked'+n for n in groups]),f'theorem coverage{tag} : records{tag}.map Certificate.ids = domain := by rfl','end TripleCertificates']
 (L/f'{name}.lean').write_text('\n'.join(t)+'\n')
print('generated balanced aggregators')
