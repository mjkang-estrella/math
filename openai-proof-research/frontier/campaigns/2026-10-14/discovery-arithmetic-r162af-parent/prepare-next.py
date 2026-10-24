#!/usr/bin/env python3
"""Prepare exact-scope research continuation; do not dispatch or change shared state."""
from pathlib import Path
import fnmatch
import hashlib
import json
import re
import subprocess

P=Path(__file__).resolve().parents[4]
B=P/'frontier/campaigns/2026-10-14'
D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162ag-parent'
R=B/'fresh-arithmetic-discovery-r162ag'
OLD=B/'fresh-arithmetic-discovery-r162af'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162ag-brief.txt'
def sha(raw):
    return hashlib.sha256(raw).hexdigest()
def dump(p,x):
    p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):
    return {g for g in re.findall(r'\*[^\s,;()]*\*',s) if g not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
raw_t=subprocess.check_output(['git','show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'],cwd=P)
raw_j=subprocess.check_output(['git','show',head+':openai-proof-research/frontier/NEW-TEN-2026-10-14.md'],cwd=P)
assert (B/'tasks.json').read_bytes()==raw_t and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()==raw_j
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P).strip()
tasks=json.loads(raw_t)
assert tasks['newAccepted']==19 and tasks['target']==20
own=next(i for i,t in enumerate(tasks['tasks']) if t.get('clientRequestId')=='twenty-20261023-fresh-arithmetic-r162af-codex-astra-r1')
names=[p.relative_to(P).as_posix() for p in [N,R,BP]]
checks=[];legacy=[]
for i,t in enumerate(tasks['tasks']):
    if i==own or t.get('status') not in {'running','queued','waiting'}:
        continue
    if 'brief' not in t:
        assert 'nativeTaskName' in t and 'taskId' not in t
        legacy.append(i);continue
    raw=(P/t['brief']).read_bytes();patterns=rules(raw.decode())
    matches={n:[g for g in sorted(patterns) if fnmatch.fnmatchcase(n.casefold(),g.casefold())] for n in names}
    assert all(matches.values()),(i,matches)
    checks.append(dict(task_index=i,original_brief=t['brief'],sha256=sha(raw),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,legacy_limit='Historical native entries lack original briefs; no live query or reopening. Recorded status is not fresh liveness.',foreign_live_queries=False)
dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists()
N.mkdir();R.mkdir();(N/'private').mkdir()
dump(N/'prospective-isolation.json',guard)

old_raw=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162af-brief.txt').read_bytes()
assert sha(old_raw)=='52dcc0d933333dbe632649dbf27ea06e4c11a99dbf979cd7f66ceea9ecf83957'
marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old_raw.split(marker,1)[1];assert len(standing)==5570
old=old_raw.decode()
historical_scopes=old[old.index('R162W is CLOSED'):old.index('Catalogue access,if needed:')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
direct=[D/'assessment.md']+[OLD/x for x in [
    'FINAL.md','REPORT.md','packet/private/prefreeze-scope.md',
    'packet/private/prefreeze-mathematics.md','packet/private/source-understanding.md',
    'packet/private/primary-understanding.md','packet/private/original-history-understanding.md',
    'packet/private/READING-LIMITS.md','packet/private/canonical-authentication.json',
    'packet/private/canonical-tree-selection.json']]
auth=json.loads((OLD/'packet/private/canonical-authentication.json').read_text());assert len(auth)==13
direct += [OLD/x['local'] for x in auth]
for stem in ['bizeul2023','bn2012v1','cfp2018','em2019v1','fms2024v1','mnr2024v2']:
    for suffix in ['pdf','txt']:
        direct.append(OLD/f'packet/private/primary/{stem}.{suffix}')
assert len(direct)==len(set(direct))
records=[]
for p in direct:
    assert p.is_file() and not p.is_symlink()
    raw=p.read_bytes();records.append(dict(path=p.relative_to(P).as_posix(),bytes=len(raw),mode=p.stat().st_mode,sha256=sha(raw)))
dump(N/'private/completed-direct-inputs.json',records)

header='''Arithmetic discovery r162ag — full entropy-overlap continuation.
Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ag/.

This is a mathematical RESEARCH follow-up in the SAME author conversation, not an independent review, a new catalogue family, or a retry of a graded proof. Your completed r162af is PREFREEZE/no nominee: no frozen theorem, author-proof nomination or mathematical gate exists. Preserve its sealed bytes and all findings. Reuse your retained actual reading and derivation context, distinguishing retained reading from fresh reading; another agent's ledger is not your proof reading.

Continue the EXACT full diagnostic C below with sustained mathematical work. Do not replace it with a scalar/product, iid, fixed-dimension, proportional-covariance, uniform-Poincare, uniformly convex, spectrally separated or small-deficit theorem. A full admissible counterexample is also meaningful research; failed proof mechanisms are not counterexamples. Do not merely rename the joint gap or repeat the already-paid reductions. The earlier distinct-family selection instructions are superseded for this continuation. Every older scope and disposition remains unchanged.

Authorized actual model is Codex / GPT-6 Astra / reasoningEffort high / serviceTier default, retained from the completed research task. Campaign 19/20, latest R041, one substantial acceptance remains. This overrides obsolete 18/20 and Factory-only lines in the verbatim standing brief. EVERY command workdir /home/mj-kang/Documents/Dev/math/openai-proof-research. Your NEW root exists empty. All scratch, temporary material, downloads, extracts, renders, copies, durable notes and seal stay inside it. No old/shared/brief/root changes, git/staging/commits, nested agents, heavy installs, unbounded jobs or downstream formal/manuscript/release work. Publication/uploads/submissions/contacts/browser UI STOPPED. Parent alone adopts gates/counts.

Retain direct AGENTS.md and sources/upstream.json. Acceptance access is ONLY frontier/NEW-TEN-2026-10-14.md[4801,6347); no whole journal/catalogue decoding or raw-byte whole-journal hashing. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb AND all operative source proofs are stipulated TRUE; do not audit upstream truth. Complete sources/preprints-tree.json has 13223 entries,4858136 bytes,SHA256 eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b. Ignore truncated tree.json. Evidence work must be proportionate; mathematics dominates.

EXACT FULL C: For EVERY n>=1 and EVERY independent pair of log-concave Borel laws X,Y on R^n, including proper affine-subspace laws and points, suppose Sigma=Cov(X)+Cov(Y)>0. Put S=X+Y and M=Sigma^(-1/2)Cov(X)Sigma^(-1/2). Seek ONE numerical c>0, independent of dimension and inputs, such that
  Delta(S)=h(S)-n-(1/2)logdet(Sigma) >= c*kappa,
  kappa=tr(M(I-M)).
Retain the ACTUAL independent pair, SAME summed law and ONE common affine normalization, arbitrary dependence within each input, every covariance spectrum and the ENTIRE deficit regime. There is no algorithmic claim. Neither C nor its negation has been proved. C remains a provisional research target; if a viable full theorem emerges, freeze its exact scope before extended full-proof drafting.

Completed r162af payments and traps (full derivations are exact admitted originals below):
1. Common whitening gives Cov(S)=I,Cov(X)=M,Cov(Y)=I-M. For spectral Q, min_Q[E||(I-Q)X||^2+E||QY||^2]=sum min(lambda,1-lambda), between kappa and2*kappa, with an exact SAME-input coupling to QX+(I-Q)Y. This equivalence and complementary-exponential zero-deficit classification are paid, not quantitative stability.
2. On the SAME source normalized sum transport, the common remainder R_source=H+D0+||Y_res||_H1^2/1500+Omega(B)/1000<=2Delta is retained with its exact definitions and coefficients. H=E tr[t(A)^2 Hess U_P(F)], A=q^(-1)(DF), E A=0, A=L+Y_res,L=sum x_r X_r,B=sum X_r^2; S0=(37I/40+3B/40)^(-1),K=S0^(1/2)Cov(F)S0^(1/2),D0=trK-logdetK-n. The sufficient J_C bridge kappa<=C0 R_source for EVERY smooth independent pair remains unpaid and is NOT asserted necessary to every possible proof. Already-spent source eigenvalue-separation surplus cannot be used twice.
3. Bizeul's ACTUAL two-law entropy jump plus scalar Cheeger/Poincare pays ALL scalar pairs, common-coordinate products and proportional-covariance inputs with controlled Poincare constant. Eigenvectors do not make dependent coordinates independent. General-covariance Follmer and uniformly convex transport arguments retain minimum-eigenvalue/Poincare/contraction factors. They cannot be silently promoted to universal constants.
4. Exact regression R=X-MS has Cov(R)=D=M(I-M),Cov(S,R)=0. For nonsingular inputs, Delta=delta_X+delta_Y-E delta_(R|S)+(logdetD-E logdet Cov(R|S))/2. The conditional deficit has a MINUS sign. The equivalent Gaussian-reference identity retains conditional means. Marginal Hessian calculation retains the negative posterior score-covariance with the SAME t(A)^2 output weight. Separate directional/posterior winners, dropping total correlation or independently spending the input budget do not close C. For 0<M<I the exact entropy-jump bookkeeping has negative L=-logdet(4M(I-M))/4 in Delta=Z-L+J; it cannot be discarded near complementary spectra.
5. Gaussian/exponential continuum calculations constrain constants but supply no counterexample. Full rough/singular transfer is paid CONDITIONALLY on a joint uniform smooth two-sided-Hessian estimate: intrinsic source approximation, independent tiny Gaussian regularization, entropy convergence using source density caps and controlled tails, and covariance/overlap convergence preserve the SAME c. No common Hessian bounds across approximants may be assumed.
6. The real unpaid operation is ONE dimension-uniform JOINT overlap bound across arbitrary covariance directions and arbitrary within-input dependence against ONE total Delta(S). Potential routes include a full-spectrum Follmer/information-production comparison, the source common-remainder J_C route with posterior subtraction, or a genuinely joint localization preserving independence/covariance. These are research suggestions, not additional hypotheses or an exhaustive list. Fixed-n compactness does not give a dimension-uniform linear rate; old unproved global exponential stability, KLS-type bounds or algebra-rounding cannot be premises.

Reading/provenance: all13 Source101 canonical blobs authenticated; COMPLETE operative text/certificate code actually read in r162af, code not executed. Six primary PDFs retrieved; Bizeul2023 fully read, others at recorded actual operative extents. Transitive ancestry remains incomplete. Reuse actual reading honestly and read any newly invoked primary proof interfaces before claiming closure. Do not spend the continuation copying the whole old corpus or redoing its administrative tests.

No catalogue navigation or new history traversal is authorized in this continuation. The one previous guarded history scan and precise original extents remain the record. Do NOT rerun/broaden it or follow old copied exceptions. Existing source/primary/history understanding records are bounded evidence, not clearance certificates. Previously admitted fetch.py/read.py,assemble_records.py,git-identities.json/original-current-bindings.json aliases, unrelated snippets and opaque unread r69 are disclosed limitations, not operative inputs. No active-peer findings/body/status/activity queries. Before creating new namespaces the parent checked their paths against recorded foreign nonterminal ORIGINAL INITIAL briefs; recorded status is not live liveness. Own r162ag I/O is explicitly authorized despite broad history guards; old r162af is strictly read-only through ONLY the exact list below.

'''
section='EXACT read-only completed input exceptions (project-relative POSIX paths):\n'
section+='\n'.join(x['path'] for x in records)
section+='''
These exact paths authorize no containing directory, linked body, previous direct exception, old parent/role/status/brief or other review. Protected bodies AND their named metadata stay PRIVATE/local under original rights. If needed, copy only a selected operative excerpt into your own private root; track original identity and actual read extent. Never attach the old manifest to a reduced selection. The retained source metadata identifies Source101's ACTUAL wrapper build/manuscript/main.tex (2110 bytes,blob208e79bad81ad827bd6da83e44332fd397714940), not guessed conventional build paths. Compiled PDF authentication is not semantic reading.

Historical full scopes/dispositions from the original research brief, preserved verbatim below, are CONTEXT ONLY. They do not reopen those targets or authorize extra paths; the exact C continuation and new write root above govern this turn:

'''
extra='\nAdditional prospective literal twins and escaped helper guards; all prior literals remain:\n*arithmetic*162af* *arithmetic*r162af* *arithmetic*162ag* *arithmetic*r162ag* *i34_target_uniform_brenier* *i55_sharp_entropy_stability_r2*\n\n'
brief=(header+section+historical_scopes+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode())
for g in ['*arithmetic*162ag*','*arithmetic*r162ag*','*arithmetic*162af*','*arithmetic*r162af*']:
    assert g in rules(brief.decode())
assert brief.split(marker,1)[1]==standing
BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,continuation=True,exact_same_full_C=True,no_new_catalogue_or_history_scan=True,source=101,canonical_blobs=13,completed_direct_inputs=len(records),parent_source_body_read=False,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),completed_exact_readonly_inputs=len(records),both_new_literal_twins_verified=True,continuation=True)))
