import pathlib,re,json,hashlib,zipfile
D=pathlib.Path(__file__).resolve().parents[1]
s=(D/'logs/lean-inventory.log').read_text()
# '#print prefix' emits one fully qualified name per declaration.
names=sorted(set(re.findall(r'R162\.[A-Za-z0-9_\.\u2080-\u2089]+',s)))
assert len(names)>150,len(names)
(D/'lean/Audit.lean').write_text('import Endpoint\n'+''.join('#print axioms '+n+'\n' for n in names))
(D/'outputs/local-declarations.json').write_text(json.dumps(names,indent=2))
print('axiom audit declarations',len(names))
# Include private module-qualified generated names as well.
names=sorted(set(re.findall(r'(?:_private\.[A-Za-z0-9_\.]+\.)?R162\.[A-Za-z0-9_\.\u2080-\u2089]+',s)))
(D/'lean/Audit.lean').write_text('import Endpoint\n'+''.join('#print axioms '+n+'\n' for n in names))
(D/'outputs/local-declarations.json').write_text(json.dumps(names,indent=2))
p=D/'lean/Audit.lean';p.write_text(p.read_text().replace('import Endpoint\n','import Endpoint\nset_option linter.auxLemma false\n'))
