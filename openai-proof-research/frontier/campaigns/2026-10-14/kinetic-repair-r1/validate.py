"""Structural and finite-support receipts only, not an analytic proof verifier."""
from pathlib import Path
import difflib,hashlib,json,re
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[3]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks={}
def ck(name,value):
    if not value: raise AssertionError(name)
    checks[name]=True
original=HERE.parent/'kinetic-window-factory/candidate.md'
review=HERE.parent/'kinetic-proof-r1/review.md'
ck('original_candidate_identity',sha(original)=='7c71805a0029bf5badcdbed37355775741e7aeb2513a3fba0a9a64b1f8fd2208')
ck('full_review_identity',sha(review)=='9333aca083f4d8428be9a45f71baf2f3a065da6443c59e99046bbe6ce1f2f2ab')
frozen=json.loads((HERE/'frozen-inputs-before.json').read_text())
ck('all_21_original_files_unchanged',len(frozen)==21 and all(sha(ROOT/r['path'])==r['sha256'] for r in frozen))
old=original.read_text();new=(HERE/'candidate.md').read_text()
ck('no_nonprinting_controls',not any(ord(c)<32 and c not in '\n\t' for c in new))
ck('balanced_display_delimiters',new.count('$$')%2==0)
ck('single_E_prime_statement',new.count('**Lemma E′.**')==1)
ck('all_original_numbered_sections',all(len(re.findall(r'^## '+str(n)+r'\.',new,re.M))==1 for n in range(9)))
ck('Q_retained_in_averaged_integral','R_G^{\\rm ext}Q_G\\prod_g' in new)
ck('prefix_flux_before_Q_dropped','Only **after this prefix bound**' in new)
ck('all_line_energy_explicit','Every\nsubset of slab-$i$ lines has energy at most $E_0$' in new)
ck('budget_before_order','Before fixing an observation list, a moment' in new)
ck('decorated_component_inversion','D^{\\mathrm{dec}}_{b,B}' in new)
ck('no_endpoint_TV_lift','This does not lift an endpoint TV estimate to histories' in new)
ck('all_count_diagonals','\\mathrm{Count}^{(3)}+3\\mathrm{Count}^{(2)}+\\mathrm{Count}' in new)
ck('uniform_topology_overclaim_removed','so the\nconvergence also holds for the uniform topology' not in new and 'in $J_1$ and in the uniform topology' not in new)
a=old.split('## 5. Chaining down to the microscopic scale\n',1)[1].split('\n## 6.',1)[0]
b=new.split('## 5. Chaining down to the microscopic scale\n',1)[1].split('\n## 6.',1)[0]
ck('original_chaining_proof_byte_preserved',a==b)
response=(HERE/'response-to-review.md').read_text()
ck('response_binds_actual_revised_hash',sha(HERE/'candidate.md') in response)
diff=''.join(difflib.unified_diff(old.splitlines(keepends=True),new.splitlines(keepends=True),fromfile='kinetic-window-factory/candidate.md',tofile='kinetic-repair-r1/candidate.md'))
(HERE/'candidate.diff').write_text(diff)
ck('response_binds_exact_diff_hash',sha(HERE/'candidate.diff') in response)
for f in json.loads((HERE/'source-H-authentication.json').read_text())['files']:
    p=ROOT/f['local_path'];data=p.read_bytes()
    ck('H_'+p.name,sha(p)==f['sha256'] and hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==f['git_blob_sha1'])
ck('reviewer_checker_copy_unchanged',sha(HERE/'checks/adversarial_checks.py')==sha(HERE.parent/'kinetic-proof-r1/adversarial_checks.py'))
ck('reviewer_exact_receipt_reproduced',sha(HERE/'checks/adversarial_checks.json')==sha(HERE.parent/'kinetic-proof-r1/adversarial_checks.json'))
r=json.loads((HERE/'checks/repair_checks.json').read_text())
ck('fourteen_exact_controls',r['status']=='PASS' and r['count']==14 and all(r['checks'].values()))
receipt={'status':'PASS','scope':'Structural/frozen-binding and exact finite supporting receipts only; not independent mathematical review or proof verification.','checks':checks,'count':len(checks),'candidate_sha256':sha(HERE/'candidate.md'),'candidate_bytes':(HERE/'candidate.md').stat().st_size,'candidate_lines':len(new.splitlines()),'full_original_scope':True,'next_gate':'Fresh independent full proof review','formal_certificate':False,'accepted':False,'public_submission':False}
(HERE/'validation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({'status':'PASS','structural_checks':len(checks),'candidate_sha256':receipt['candidate_sha256'],'frozen_files_unchanged':21,'exact_new_controls':14}))
