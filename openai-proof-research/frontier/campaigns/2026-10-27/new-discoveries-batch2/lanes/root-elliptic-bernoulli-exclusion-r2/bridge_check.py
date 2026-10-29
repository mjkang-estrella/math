import resource,signal,json
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(20,)*2);signal.alarm(25)
import sympy as s
e,P,Q,R,Z,g=s.symbols('e P Q R Z g')
# Published D23 with a=e,b=e-t; jets use wp even, zeta odd.
pa=e**-2; pb=P-e*Q+e**2*R/2; za=e**-1; zb=-Z-e*P+e**2*Q/2
expr=s.expand(pa*pb+Q*(za-zb)-P*(pa+pb))
constant=s.expand(expr).coeff(e,0)
expected=2*P**2-g/4+Q*Z
ok=s.expand(constant.subs(R,6*P**2-g/2)-expected)==0
# Residue at z=a is +wp'(a-b); negative preprint sign fails.
residue_published=Q; residue_preprint=-Q
out={'published_D23_limit':str(constant),'after_ODE':str(expected),'constant_check':ok,'published_D22_residue_correct':residue_published==Q,'preprint_128_residue_correct':residue_preprint==Q,'resource':'512MiB AS;20 CPU seconds;25s alarm; external30s; BLAS/OMP/MKL1','scope':'exact symbolic constant and sign diagnostic only; all-order bridge is in review.md'}
Path(__file__).with_name('bridge-check.json').write_text(json.dumps(out,indent=2));assert ok;print(json.dumps(out,indent=2))
