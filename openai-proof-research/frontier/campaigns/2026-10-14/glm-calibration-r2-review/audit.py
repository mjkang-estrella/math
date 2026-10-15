"""Parent independent checks of the specific GLM round-2 repairs."""
from pathlib import Path
import contextlib, hashlib, importlib.util, io, json, os, tempfile
import sympy as s

HERE=Path(__file__).resolve().parent
subject=HERE.parent/'glm-calibration-r2/check.py'
spec=importlib.util.spec_from_file_location('glm_r2_subject', subject)
m=importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
R=s.Rational
N=s.zeros(6)
for i,j,v in [(0,1,R(6,5)),(0,3,s.sqrt(14)/5),(1,2,R(8,5)),
              (3,2,-3*s.sqrt(14)/20),(3,4,R(5,4)),(4,5,s.sqrt(2))]: N[i,j]=v
C=[s.zeros(2),s.Matrix([[0,0],[s.sqrt(7)/4,0]]),s.diag(R(3,4),-R(3,4)),s.Matrix([[0,s.sqrt(7)/4],[0,0]])]
def eq(a,b): return all(s.simplify(x)==0 for x in a-b)
P=sum((s.kronecker_product(N**k,C[k]) for k in range(4)),s.zeros(12))
F=sum((s.kronecker_product(C[k],N**k) for k in range(4)),s.zeros(12))
J=s.zeros(12)
for old in range(12):
    i,j=divmod(old,2); J[6*j+i,old]=1
x=s.zeros(12,1); x[4]=x[11]=1/s.sqrt(2)
y=s.zeros(12,1); y[0]=1/s.sqrt(2); y[3]=s.sqrt(7)/s.sqrt(2)/5; y[7]=-R(3,5)
assert eq(m.build_N(),N)
assert all(eq(a,b) for a,b in zip(C,m.build_Cks()))
assert eq(m.build_PN(N,C),P) and eq(m.build_PN_fiberfirst(N,C),F)
assert eq(F,J*P*J.T) and eq(J.T*J,s.eye(12))
assert eq(P*x,2*y) and eq(F*(J*x),2*J*y)
residual=s.simplify(((F*x-2*y).T*(F*x-2*y))[0])
assert s.simplify(residual-(R(2099,512)-129*s.sqrt(14)/256))==0 and residual!=0

# Actual-input rank control after a baseline computation; no cached reuse.
baseline=m.cyclic_profile(N)
zero=m.cyclic_profile(s.zeros(6))
red=s.zeros(6); red[0,1]=1; red[2,3]=2
reducible=m.cyclic_profile(red)
# This independent Hermitian control has cyclic e1 but a commutative algebra.
path=s.zeros(6)
for i in range(5): path[i,i+1]=path[i+1,i]=1
cyclic_reducible=m.cyclic_profile(path)
assert baseline==({0:1,1:2,2:3,3:5,4:6,5:6},4,36)
assert zero==({i:1 for i in range(6)},None,1)
assert reducible==({0:1,1:2,2:2,3:2,4:2,5:2},None,9)
assert cyclic_reducible==({i:i+1 for i in range(6)},5,6)
assert not m.cert_Cyclic_rank(s.zeros(6),C)[0]
assert m.cyclic_profile(N)==baseline

# Verify the exported word certificate by multiplying its words independently.
record=json.loads((HERE.parent/'glm-calibration-r2/results.json').read_text())
cert=record['base_case']['checks']['Irreducibility_rationalized']['data']
D=s.diag(1,1,1,s.sqrt(14),s.sqrt(14),s.sqrt(7))
A=D.inv()*N*D; B=D.inv()*N.T*D
columns=[]
for name in cert['basis_words']:
    assert name.startswith('identity')
    W=s.eye(6)
    for letter in name[len('identity'):]:
        assert letter in 'NS'
        W=W*({'N':A,'S':B}[letter])
    columns.append(s.Matrix(list(W)))
assert len(columns)==36
basis=s.Matrix.hstack(*columns)
det=basis.det(method='domain-ge')
assert det==R(2733816767052433962421431,576460752303423488)
assert s.sympify(cert['nonzero_36x36_basis_determinant'])==det

# The old PSD helper accepted this non-Hermitian matrix from its minors.
try:
    m.psd_hermitian(s.Matrix([[1,1],[0,1]]))
except ValueError as e:
    assert 'not Hermitian' in str(e)
else: raise AssertionError('Hermiticity guard absent')
assert m.psd_hermitian(s.eye(2))
assert not m.psd_hermitian(s.diag(1,-1))

# Exercise the real top-level exit logic with synthetic battery outcomes.
# This tests error classification, not any mathematical certificate.
actual_battery=m.run_battery
original_checks=m.CHECKS
m.CHECKS=[('sentinel',lambda *_: (_ for _ in ()).throw(RuntimeError('injected')))]
err=m.run_battery(N,C)['sentinel']
assert err['status']=='FAIL' and err['failed_by']=='exception'
m.CHECKS=original_checks
exits={}
for inject_exception in [False,True]:
    calls=[0]
    def fake_battery(*_):
        k=calls[0]; calls[0]+=1
        outcomes={cid:{'status':'PASS','failed_by':None,'detail':'synthetic','seconds':0} for cid,_ in original_checks}
        if k:
            mut=m.MUTANTS[k-1]
            for cid in mut['expected_fail']:
                outcomes[cid].update(status='FAIL',failed_by='comparison_mismatch')
            if inject_exception and k==1:
                outcomes[mut['expected_fail'][0]]['failed_by']='exception'
        return outcomes
    m.run_battery=fake_battery
    with tempfile.TemporaryDirectory(prefix='glm-harness-audit-') as tmp:
        old=os.getcwd(); os.chdir(tmp)
        try:
            with contextlib.redirect_stdout(io.StringIO()): rc=m.main()
        finally: os.chdir(old)
    exits[str(inject_exception)]=rc
assert exits=={'False':0,'True':2}
m.run_battery=actual_battery

# Provenance includes the actual subject and remains valid for unchanged inputs.
for name,recorded in record['meta']['provenance_sha256'].items():
    assert 'error' not in recorded,name
    path=(subject.parent/recorded['path']).resolve()
    assert hashlib.sha256(path.read_bytes()).hexdigest()==recorded['sha256'],name

result={'subject_sha256':hashlib.sha256(subject.read_bytes()).hexdigest(),
        'tensor_repair':'PASS; independent Kronecker construction and flip',
        'unpermuted_residual_squared':str(residual),
        'baseline_profile':baseline,'zero_profile':zero,'reducible_profile':reducible,
        'cyclic_but_reducible_hermitian_profile':cyclic_reducible,
        'exported_word_basis_determinant':str(det),
        'hermiticity_guard':'PASS','synthetic_main_exit_codes':exits,
        'provenance':'all recorded inputs match','base_certificate_count':len(original_checks),
        'notes':['Three new certificates, not four: 21+3=24.',
                 'Sampling does not certify universal scalar compression.',
                 'No new mathematical result or model-reliability claim.']}
(HERE/'targeted-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
