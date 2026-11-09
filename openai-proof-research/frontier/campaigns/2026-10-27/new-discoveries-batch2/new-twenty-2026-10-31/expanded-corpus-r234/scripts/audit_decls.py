import pathlib,re
D=pathlib.Path(__file__).resolve().parents[1];s=(D/'lean/Hurlbert.lean').read_text();names=re.findall(r'^(?:def|theorem)\s+(\w+)',s,re.M)
(D/'lean/Audit.lean').write_text('import Hurlbert\n'+''.join('#print axioms MathDB356266.'+n+'\n' for n in names)+'\n#print MathDB356266.counterexample\n')
print(names)
