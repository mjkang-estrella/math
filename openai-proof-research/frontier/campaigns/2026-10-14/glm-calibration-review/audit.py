#!/usr/bin/env python3
"""Independent targeted audit; never writes to the subject directory."""
import hashlib,json,runpy,time
from pathlib import Path
import sympy as s
R=Path(__file__).resolve().parent
m=runpy.run_path(str(R/'subject-check.py'))
N=m['build_N']();C=m['build_Cks']();PN=m['build_PN'](N,C)
eq=m['exact_eq'];x=m['vec_x']();y=m['vec_y']()
result={'sympy':s.__version__}
# A genuine fiber-first assembly, with the correct six-dimensional stride.
F=sum((s.kronecker_product(C[k],N**k) for k in range(4)),s.zeros(12))
J=s.zeros(12)
for i in range(6):
 for j in range(2):J[6*j+i,2*i+j]=1
assert eq(F,J*PN*J.T)
assert eq(F*(J*x),2*J*y)
broken=m['build_PN_fiberfirst'](N,C)
assert not eq(broken,F)
result['tensor']={'base_first_matches_independent_kronecker':eq(PN,sum((s.kronecker_product(N**k,C[k]) for k in range(4)),s.zeros(12))),
 'correct_fiber_first_matches_flip':True,'correct_fiber_first_attains_with_permuted_vectors':True,
 'subject_fiber_builder_matches_true_fiber_first':False,
 'subject_wrong_builder_nonzero_rows':[i for i in range(12) if any(broken[i,j]!=0 for j in range(12))],
 'subject_vs_true_nonzero_difference_entries':sum(not eq(broken[i,j],F[i,j]) for i in range(12) for j in range(12)),
 'true_fiber_first_fails_with_unpermuted_vectors':not eq(F*x,2*y),
 'subject_wrong_builder_residual_norm2':str(s.simplify(((broken*x-2*y).conjugate().T*(broken*x-2*y))[0])),
 'true_fiber_first_unpermuted_residual_norm2':str(s.simplify(((F*x-2*y).conjugate().T*(F*x-2*y))[0]))}
# Independent rationalization: simultaneous similarity of N and N*.
D=s.diag(1,1,1,s.sqrt(14),s.sqrt(14),s.sqrt(7));A=D.inv()*N*D;B=D.inv()*N.T*D
assert all(z.is_Rational for z in A) and all(z.is_Rational for z in B)
words=[('',s.eye(6))];front=[('',s.eye(6))];dims=[]
for length in range(7):
 if length:
  front=[(w+'N',v*A) for w,v in front]+[(w+'S',v*B) for w,v in front]
  words+=front
 V=s.Matrix.hstack(*(s.Matrix(list(v)) for w,v in words))
 rank=V.rank();dims.append(rank)
 if length==6:
  _,piv=V.rref();basis=V[:,list(piv)];det=s.factor(basis.det(method='domain-ge'))
  assert rank==36 and det!=0
result['algebra_span']={'similarity_D_diagonal':[str(z) for z in D.diagonal()],
 'rational_N':[[str(z) for z in A.row(i)] for i in range(6)],
 'rational_Nstar':[[str(z) for z in B.row(i)] for i in range(6)],
 'word_space_dimensions_lengths_0_through_6':dims,
 'basis_words':['identity' if not words[i][0] else words[i][0] for i in piv],
 'basis_word_convention':'Words multiply left-to-right; N=A, S=B; original matrices are simultaneously similar by D.',
 'nonzero_36x36_basis_determinant':str(det)}
# Detect baseline-only rank helper by feeding a zero input to the certificate.
zero_ok,zero_detail=m['cert_Cyclic_rank'](s.zeros(6),C)
result['baseline_word_cache_defect']={'subject_certificate_on_zero_matrix_passes':zero_ok,
 'subject_certificate_on_zero_matrix_detail':zero_detail,
 'actual_zero_matrix_cyclic_dimension':1,'actual_zero_matrix_unital_algebra_dimension':1}
assert 'dim6=36' in zero_detail and not zero_ok
# Exact graph of N^3 and mutation sensitivity, independently of the report.
Nm=m['build_N']({(0,1):s.Rational(6,5)+s.Rational(1,20)})
assert eq(Nm**3,N**3)
assert not eq(m['build_PN'](Nm,C)*x,2*y)
result['N12_mutation']={'N_cubed_unchanged':True,'PNx_attainment_broken':True}
# PSD helper's caller always produces Hermitian matrices, but helper has no guard.
nonherm=s.Matrix([[1,1],[0,1]])
result['PSD_helper_precondition']={'rejects_nonhermitian_matrix':not m['psd_hermitian'](nonherm),'actual_calibration_calls_form_G_as_alpha_I_minus_Mstar_M':True}
# Universal operator ingredients independent exact inequality from the proof.
G=PN.T*PN;xx=x*x.T
H=s.Rational(337,128)*s.eye(12)+(4-s.Rational(337,128))*xx-G
assert H==H.T and H.is_positive_semidefinite is True
result['universal_bound_ingredients']={'G_leq_337over128_I_plus_175over128_xxstar':True,
 'x_fiber_gram_is_half_identity':eq(s.Matrix(6,2,list(x)).T*s.Matrix(6,2,list(x)),s.eye(2)/2),
 'half_overlap_bound_arithmetic':str(s.Rational(4,2)+s.Rational(337,256)),
 'all_complex_product_vector_inference':'Requires Schmidt overlap <=1/2 and output contraction; these are mathematical arguments, not 36 samples.'}
(R/'targeted-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
