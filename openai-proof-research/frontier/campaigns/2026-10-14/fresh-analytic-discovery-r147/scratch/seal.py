from pathlib import Path
import json,hashlib,os
R=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r147')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
assert not (R/'MANIFEST.json').exists()
with (R/'CHRONOLOGY.md').open('a') as f:f.write('\n9. Final byte checks matched all17 pinned source bodies against the complete tree,4 incoming primary objects/3 selected TeX members,13 whole originals plus2 excerpts since late capture,unchanged frozen statement/checkpoint. Six copied integrity controls accepted baseline/restored and rejected changed/missing/hidden-extra/wrong-anchor states, with before/after snapshot equality for every verifier invocation. No mathematical gate. Sealing follows once; final detached hashes and read-only verification are external terminal outputs.\n')
statement=sha(R/'STATEMENT.md');proof=sha(R/'AUTHOR-PROOF.md')
final=f'''# T360S147 — full author-proof nominee

Exact full statement: STATEMENT.md, SHA256 `{statement}`.
Author proof: AUTHOR-PROOF.md, SHA256 `{proof}`.

For every closed connected smooth weak-MTW Riemannian manifold of dimension n>=2, the optimal homeomorphisms between arbitrary positive bounded measurable probability densities are globally W1,1 in both directions, with a geometry-only bound on the sum of the derivative L1 norms. Conjugate contacts are permitted; no orientability or cut-separation assumption is added.

The integrated proof uses Source360's unique log/full midpoint graph, De Philippis–Figalli's local smooth-cost Sobolev theorem, and the exact cancellation Q adj(P)=0 for PSD P,Q with singular broken-action Hessian P+Q. A distributional Piola/area formula transfers this cancellation to the full derivative measure on the focal set. The initial concentration gap is paid; no positive midpoint-density floor or global nondegenerate cost chart is assumed.

The author has no known unpaid mathematical obligation at this frozen scope. Independent correctness and substantial-contribution reviews are UNREVIEWED. The specific contribution question is whether the weighted-cofactor removal is nonroutine after the strongest compatible source/classical composition. No substantial grade, acceptance, count, priority/current-open/exhaustive-search claim, or downstream stage is assigned. Parent alone integrates, reviews and counts. See GAPS.md and CONTRIBUTION.md.

Actual partial source/transitive read extents, late recoveries, catalogue incidental displays, broad-scan false admissions/truncation and rights limits are in READING-LIMITS.md and ISOLATION.md. The frozen statement was not weakened or rewritten. Old I07/I225/I331 and all user-protected full scopes/dispositions remain unchanged.

Only this exclusive r147 root was written. Publication/uploads/submissions/contacts/browser UI remain stopped. Provenance: authorized Codex/GPT-6 Astra/high/default service tier; runtime Astra/high, tier not independently observed. Campaign19/20/latestR041.

MANIFEST.json enumerates exact payload membership and excludes exactly FINAL.md,MANIFEST.json,REPORT.md. Detached SHA256 anchors for those three envelopes are provided externally. verify.py requires those explicit anchors and is read-only. Integrity checks and finite matrix diagnostics are not mathematical gates.
'''
report=f'''# Outside-payload report

T360S147 is a full author-proof nominee, not a gate verdict. The exact frozen statement has SHA256 `{statement}` and the author proof has SHA256 `{proof}`. Its full rough-density/global-bi-W1,1 scope is unchanged; no old target is replaced.

Mathematical reduction: singleton lifted contact logs -> geometric Lipschitz midpoint endpoints X,Y -> positive semidefinite P,Q with dX=L_X P,dY=L_Y Q -> singular P+Q at full conjugacy -> Q adj(P)=0 -> zero focal part of the distributional measure X_#(dY adj(dX) dz). DPF local Sobolev regularity on the genuine non-cut open region completes global membership. Reversal gives the inverse and geometry-only norm bounds. See AUTHOR-PROOF.md for the exact metric/coordinate factors and nonorientable treatment.

No mathematical gap is knowingly left in the author proof. The nonroutine/substantial contribution case is unresolved and expressly separated from proof closure. Strongest compatible source/classical operations are fully credited in CONTRIBUTION.md. There is no independent correctness review, formal proof, manuscript/release, acceptance, count or priority claim.

Authentication matched17 canonical pinned source bodies with complete13223-entry tree metadata,path,size,GitblobSHA1 and SHA256;4 incoming primary objects and3 selected members;13 whole original copies and2 independently enumerated excerpts since their late capture. Incoming-original authentication is separate from copy membership. Frozen statement and prefreeze checkpoint stayed unchanged. All protected upstream/primary/history/search/render/copied-control bodies remain private/local under original rights.

Nine exact Fraction matrix cases and three hypothesis/order diagnostics support only finite algebra. Six independently manifested copied-fixture controls accepted baseline/restored and rejected changed payload,missing payload,hidden extra and incorrect detached manifest anchor. Each invocation left its current fixture unchanged. Sympy was unavailable; no installation was performed.

Limits include incomplete Holder spectral/scalar/jet proof-chain reads,partial FKM transitive reads,partial CEMS rendering,and unacquired DFS/other classical original chains. Source and primary bytes retained do not imply full semantic reading. Broad pre-descent exclusions were present from the first project-root traversal; opaque derivative/shared-status false admissions and clipped output remain disclosed. No perfect isolation,exhaustive search or literature clearance is certified.

This report,FINAL.md and MANIFEST.json are the three outside-payload envelopes. All other regular files are enumerated exactly by MANIFEST.json. The detached SHA256 anchors are computed separately in the terminal, and verify.py checks them without writes. It does not certify file modes,hardlinks,empty directories or mathematics. No seal writer is to be rerun on the sealed original.
'''
for name,body in [('FINAL.md',final),('REPORT.md',report)]:
 with (R/name).open('x') as f:f.write(body)
rows=[]
for base,dirs,files in os.walk(R,followlinks=False):
 for n in dirs:assert not (Path(base)/n).is_symlink()
 for n in files:
  p=Path(base)/n;assert not p.is_symlink();rel=p.relative_to(R).as_posix()
  if rel in ['FINAL.md','MANIFEST.json','REPORT.md']:continue
  rows.append({'path':rel,'size':p.stat().st_size,'sha256':sha(p)})
rows.sort(key=lambda x:x['path'])
with (R/'MANIFEST.json').open('x') as f:json.dump({'schema':'exact-payload-v1','excluded_envelopes':['FINAL.md','MANIFEST.json','REPORT.md'],'files':rows},f,indent=2);f.write('\n')
print(json.dumps({'payload_files':len(rows),'whole_root_files':len(rows)+3,'statement_sha256':statement,'author_proof_sha256':proof,'sealed_once':True}))
