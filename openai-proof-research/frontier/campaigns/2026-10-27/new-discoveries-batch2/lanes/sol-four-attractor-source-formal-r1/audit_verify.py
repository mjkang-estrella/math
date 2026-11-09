from pathlib import Path
import json,re,collections
root=Path(__file__).resolve().parent
s=(root/'Audit.log').read_text()
blocks=re.split(r'(?m)^DECL\|',s)[1:]
assert blocks
counts=collections.Counter();names=[];axioms=set()
for b in blocks:
 head=b.splitlines()[0].split('|')
 name,_,origin,_,unsafe=head
 assert unsafe=='false',head
 assert name not in names;names.append(name);counts[origin]+=1
 safety=re.search(r'(?m)^SAFETY\|'+re.escape(name)+r'\|([^\n]+)',b)
 assert safety and safety[1] in ['Lean.DefinitionSafety.safe','nondefinition'],(name,safety)
 a=re.search("'"+re.escape(name)+r"' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])",b)
 assert a,name
 if a[2]:
  aa={re.sub(r'\.\{[^}]*\}','',v.strip()) for v in a[2].split(',')}
  assert aa <= {'propext','Classical.choice','Quot.sound'},(name,aa)
  axioms |= aa
 assert re.search(r'(?m)^'+re.escape(name)+r'(?: |\.|\n|\{|\()',b),name
assert set(counts)=={'Closure','Words','Geometry','Attractor','Endpoint'}
assert 'FourAttractor.source_refuted' in names
assert 'FourAttractor.definition3' in names
for mod in counts:
 src=(root/(mod+'.lean')).read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|unsafe|partial)\b',src),mod
out={'status':'PASS','declarations':len(names),'origins':dict(counts),'axioms':sorted(axioms),'unsafe':[],'partial':[],'all_owned_including_generated':True}
(root/'audit-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
