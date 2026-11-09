import pathlib,json,runpy,hashlib
L=pathlib.Path(__file__).resolve().parent
# Import without re-running the diagnostic writer.
ns={'__file__':str(L/'lasso.py')};exec((L/'lasso.py').read_text().split('failed=L/')[0],ns)
cover=ns['cover'];absent=ns['absent']
assert cover('abbab','abb','abbab')
assert not cover('yx','y','y')
assert absent('yx','y')=='yxy'
# Return-word decoder tau(x)=ab,tau(y)=abb, input y x y^omega.
# y occurs twice in q-image but x only once in the input.
row={'decoder':{'x':'ab','y':'abb'},'input_u':'yx','input_v':'y','image_u':'abbab','image_v':'abb','image_q':'abbab','cover':True,'input_nonquasiperiodic_reason':'Every prefix containing x occurs at most once; prefix y fails at x.','consequence':'Even a delimiter return-word code with bounded block lengths can introduce quasiperiodicity. This is NOT a counterexample to the fixed-point conjecture.'}
(L/'return-code-obstruction.json').write_text(json.dumps(row,indent=2))
data=json.loads((L/'lasso-checks.json').read_text());extra=[]
for r in data['witnesses']:
 if r['a']=='aba' and r['b']=='b':extra.append(r)
print('Return-code obstruction certified; sample fixed-point map witness:',extra)
# Verify all frozen originals/copies and record content-type failure honestly.
bindings=json.loads((L/'frozenbindings.json').read_text())
for r in bindings:
 for key in ['original','copy']:
  assert hashlib.sha256(pathlib.Path(r[key]).read_bytes()).hexdigest()==r['sha256']
p=L/'primary/morphism-published.pdf'
print('Published retrieval starts:',repr(p.read_bytes()[:40]),'is_pdf',p.read_bytes().startswith(b'%PDF-'))
