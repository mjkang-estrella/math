#!/usr/bin/env python3
"""Prepare one distinct research brief after original-brief guard checks; no dispatch."""
from pathlib import Path
import fnmatch
import hashlib
import json
import re
import subprocess

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
D = Path(__file__).resolve().parent
N = B / 'discovery-arithmetic-r162ab-parent'
R = B / 'fresh-arithmetic-discovery-r162ab'
brief_path = B / 'expanded-target-2026-10-17/fresh-arithmetic-r162ab-brief.txt'
def sha(data):
    return hashlib.sha256(data).hexdigest()
def git(*args):
    return subprocess.check_output(['git', *args], cwd=P)
def dump(path, value):
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')

head = git('rev-parse', 'HEAD').decode().strip()
task_path = 'frontier/campaigns/2026-10-14/tasks.json'
raw_tasks = git('show', head + ':openai-proof-research/' + task_path)
assert (P / task_path).read_bytes() == raw_tasks
tasks = json.loads(raw_tasks)['tasks']
names = [N.relative_to(P).as_posix(), R.relative_to(P).as_posix(), brief_path.relative_to(P).as_posix()]
checks = []
legacy_native_without_original_brief = []
for i, t in enumerate(tasks):
    if i == 709 or t.get('status') not in {'queued', 'running', 'waiting'}:
        continue
    if 'brief' not in t:
        assert 'nativeTaskName' in t and 'taskId' not in t
        legacy_native_without_original_brief.append(i)
        continue
    original = P / t['brief']
    data = original.read_bytes()
    patterns = [p for p in re.findall(r'\*[^\s,;()]*\*', data.decode()) if p not in {'*', '**'}]
    matches = {n: [p for p in patterns if fnmatch.fnmatchcase(n.casefold(), p.casefold())] for n in names}
    assert all(matches.values()), (i, matches)
    checks.append(dict(task_index=i, original_brief=t['brief'], sha256=sha(data), matches=matches))
guard = dict(head=head, before_creation=True, namespaces=names, original_foreign_brief_guard_checks=checks, legacy_native_without_original_brief=legacy_native_without_original_brief, legacy_limit='Historical native entries lack original briefs and were not queried or reopened; committed native_live list is empty. This is recorded metadata, not fresh liveness.', foreign_live_queries=False, parent_coordination_limit='An unnecessary full current_work_snapshot print decoded committed coordination metadata and was tool-truncated. No live foreign query or foreign packet-body read occurred; it supplies no mathematical premise or clearance. Subsequent reads use exact fields only.')
dump(D / 'integration-guard.json', guard)
assert not N.exists() and not R.exists() and not brief_path.exists()
N.mkdir(); R.mkdir(); (N / 'private').mkdir()
dump(N / 'prospective-isolation.json', guard)

old_raw = (B / 'expanded-target-2026-10-17/fresh-arithmetic-r162aa-brief.txt').read_bytes()
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing = old_raw.split(marker, 1)[1]
assert len(standing) == 5570
old = old_raw.decode()
prefix = old[:old.index('Catalogue access,if needed:')]
prefix = prefix.replace('Arithmetic discovery r162aa — confirmed covering-density operative-proof discovery.', 'Arithmetic discovery r162ab — confirmed subgaussian log-Sobolev operative-proof discovery.')
prefix = prefix.replace('fresh-arithmetic-discovery-r162aa/', 'fresh-arithmetic-discovery-r162ab/').replace('Own r162aa is excluded', 'Own r162ab is excluded')
prefix = prefix.replace('ONE distinct Source092 family with TWO confirmed companions', 'ONE distinct Source093 family with ONE confirmed canonical manuscript')
prefix = prefix.replace("every current recorded foreign nonterminal task's ORIGINAL INITIAL brief", "every current recorded T3 foreign nonterminal task's ORIGINAL INITIAL brief")
isolation = old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
previous = '''Arithmetic162aa is CLOSED PREFREEZE/no nominee, with no frozen theorem or gate. Preserve its FULL diagnostic: numerical c>0,n0 such that EVERY integer n>=n0 admits ONE bounded full-dimensional origin-symmetric RATIONAL polytope P_n with <=2n^2 facets and unrestricted translative covering density >=c n log n. Use the SAME actual body volume and source centered-cube limsup center intensity against EVERY locally finite translative covering,including boundaries;no lattice/coset/separation/aspect-ratio/favorable-n restriction or polynomial bit algorithm. Exact finite-window equivalence requires EVERY finite center list covering Q_L to satisfy m|P_n|>=c n log n(2L)^n for EVERY L>0. Source single-lattice upper and symmetric unrestricted lower n-log-n theorems,exp((n/2)log n+O(n))-facet rationalization with O(log n) scalar bits,same-body periodization/boundary collar,and fractional density one are PAID. The sparse mean-n^2/2 slab model gives positive-probability <=2n^2 facets,outer radius2a_n and volume floor(1/8)omega_n a_n^n at a_n~sqrt(n/(4log n));same-facet rationalization is paid. Average cap-hit costs/expected clipped volumes do not give the common deterministic witness. The full ONE-body/EVERY-center joint volume-normalized obstruction remains unpaid. Fixed-height source decoupling,unconditional doubly-exponential tails in an artificially capped model,and general product lower multiplicativity cannot be imported unchanged. Their failures and a near-ball sandwich facet obstruction do NOT disprove the full diagnostic;conditional joint estimates remain possible. The old r105 full maximum-multiplicity single-lattice direction was identified and NOT retried. Canonical reading is complete,primary/transitive reading incomplete;opaque helper/status possible false admissions and parent brief-display recovery are disclosed. Parent accidentally printed the full committed coordination snapshot,which decoded extra administrative summaries and was tool-truncated;no live foreign query or foreign packet-body read occurred,and no mathematical premise or isolation clearance follows. Do not repeat it. All previous scopes and dispositions remain immutable.

'''
direct = [D / 'assessment.md', B / 'fresh-arithmetic-discovery-r162aa/FINAL.md', B / 'fresh-arithmetic-discovery-r162aa/packet/private/prefreeze-mathematics.md', B / 'fresh-arithmetic-discovery-r162aa/packet/private/primary-understanding.md', B / 'fresh-arithmetic-discovery-r162aa/packet/private/READING-LIMITS.md']
direct_records = []
for p in direct:
    data = p.read_bytes()
    direct_records.append(dict(path=p.relative_to(P).as_posix(), bytes=len(data), mode=p.stat().st_mode, sha256=sha(data)))
dump(N / 'private/completed-direct-inputs.json', direct_records)
selected = json.loads((D / 'private/intake/Source093-selection.json').read_text())
assert len(selected['folders']) == 1
blobs = [x for x in selected['entries'] if x['type'] == 'blob']
assert len(blobs) == 13 and len(selected['entries']) == 17
wrapper = next(x for x in blobs if x['path'].endswith('/build/main.tex'))
section = '''Catalogue access,if needed: ONLY binary seek/read sources/CONTENTS.md[155355,156394),EXACT Source093 body. Parent decoded only the FIRST TWO numeric-bold title strings from ONE bounded14000-byte window starting155355,then selected ONLY093 body as a distinct family. Source094's body was NOT decoded or selected. No child title locator,extra family,catalogue screen,ancestor hunt or whole-catalogue opening/decoding. The one confirmed folder has13 blobs/17 complete-tree entries including roots. Parent source-body reading:NONE. Metadata is navigation,not a theorem/proof interface. An initial metadata parser expected an absolute /preprints/ component instead of the actual relative preprints/ URL; it returned zero entries and was corrected from the SAME saved selected body. No extra body or wrapper was guessed.

Read these FIVE exact COMPLETED originals as narrow direct exceptions relative to frontier/campaigns/2026-10-14/:
''' + '\n'.join(p.relative_to(B).as_posix() for p in direct) + '''
These exact exceptions never authorize containing namespaces,links,other copied/source bundles,role/brief/status/activity aliases or other peer findings. Protected completed bodies AND named metadata remain PRIVATE/local under original rights;any copies stay inside your own root. No old r105,r35,R041,weighted Brunn-Minkowski or any prior exact-body exception propagates. Do not repeat or broaden an old scan.

Your ONE developed family is SOURCE093: DIMENSION-FREE LOGARITHMIC SOBOLEV INEQUALITIES FOR SUBGAUSSIAN LOG-CONCAVE MEASURES. The pinned manuscript AND ALL operative source proofs are stipulated TRUE,including formerly conjectural conclusions. Validate exact applicability and fresh deductions,not upstream truth.

Confirmed canonical folder and actual wrapper metadata:
''' + selected['folders'][0] + '\n' + wrapper['path'] + f"\nbytes {wrapper['size']}; Git blob {wrapper['sha']}.\n\n" + '''Authenticate ALL13 canonical blobs using complete-tree size/Git blob/SHA256,including README,compiled PDF,figure,typography,reference file,wrapper and seven actual section files. Read the COMPLETE actual theorem/proof body and EVERY nested operative mathematical include,required companions,strongest relevant ACTUAL primary mechanisms and eligible ORIGINAL-history sections BEFORE extended deductions or author drafting. Follow actual include paths rather than filename conventions. All seven section bodies must be read,not just theorem statements or an extracted introduction. Distinguish semantic proof reading from duplicate PDF/typography/ancillary authentication. Do not rerun source code or audit stipulated upstream truth. Recover clipped seams; record durable mathematical understanding,exact labels,versions/URLs/read extents,access failures and unread ancestry. Mathematics must dominate proportionate evidence work.

The ENTIRE headline is PAID: EVERY centered log-concave probability measure with a Lebesgue density on R^n and linear subgaussian parameter a satisfies Ent_mu(f^2)<=C a^2 integral|Df|^2 dmu for EVERY compactly supported smooth f,with ONE universal C independent of dimension. Read the ACTUAL definition/normalization of a,hypotheses,dimension range and stronger operative conclusions before use. This resolves the stipulated subgaussian log-concave dimension-free logarithmic Sobolev conjecture. Do not nominate the headline,another normalization,an affine/isotropic reformulation,a smooth special case or classical consequences already paid by it.

The source's ENTIRE calculus,critical,prediction,hierarchy,matrix and observation operations are paid WHERE ACTUALLY PROVED; section filenames alone are not proof reading. First understand their exact common measure,conditioning,stopping,tilt,entropy,energy and parameter interfaces. Read actual strongest primary stochastic-localization,log-concave functional-inequality and entropy/transport proofs whenever invoked. Compatible classical tensorization,linear/affine changes,limits,LSI-to-concentration/transport/hypercontractivity,perturbation and conditional/marginal operations are PAID whenever their hypotheses and constants match. A failed naive route does not show the strongest classical/source composition fails. In particular,do not infer a uniform conditioned or tilted subgaussian parameter from an unconditioned marginal estimate without paying that interface;equally,credit any stronger operation already supplied by the full source proof.

Track centered versus translated measures,ambient versus affine support,Lebesgue density versus singular limits,log-concavity versus mixtures,linear-marginal subgaussian bounds versus all-Lipschitz concentration,and scalar versus matrix/conditional inequalities. Keep the SAME law,tilt/conditioning normalization,mean/covariance,entropy/Dirichlet budget,dimension constants and probability event throughout every transfer. An inherited compact-support smooth-test inequality must be extended to rough/vector/operator/conditional inputs by its full compatible proof if claimed. Existence of an analytic constant does not itself provide a polynomial oracle or bit algorithm. No altered entropy,extra uniform Hessian bound,bounded-support assumption,conditioning-probability floor,favorable marginal class or easier range may silently replace a frozen full target.

A distinct quantitative,relative,coherent-family,algorithmic,hypothesis-removal or structural operation is eligible only after a CLOSED identifiable nonroutine step survives the strongest compatible source/primary reduction. Numerical evidence,optimized classical constants,equivalent formulations,source-dependent notation and difficult unproved conjectures are not findings. Preserve every old full target and closed disposition. On overlap inspect eligible ACTUAL original-history mechanisms under the prospective guards; exact completed exceptions never open linked protected namespaces.

After complete operative reading choose and develop ONE distinct fully specified full-scope operation with sustained CONCRETE mathematics beyond a first failed shortcut. Try the strongest integrated source/primary payment before naming a bridge unpaid. Keep actual laws,common witnesses,parameters,entropy/energy/probability budgets and all compatibility interfaces. Preserve paid derivations,failed attempts and precise residuals. Freeze a viable exact theorem BEFORE author-proof development,then close every quantifier/constant/interface. If nothing closes,honest PREFREEZE/no nominee with exact gaps;no weaker substitute,self-grade,count,exhaustive clearance,global impossibility or worldwide-priority claim.

Keep all source/primary/history/search/extract/render/copied bodies AND named metadata PRIVATE/local under original rights. Prospectively serialize EVERY literal wildcard/substring rule below before optional filename traversal/body selection beyond narrow exceptions,retaining r/no-r,flat/compound/role aliases. At most ONE correctly pruned original-history traversal with no size/extension cutoff on eligible authored UTF8 after pruning;no projectwide rg-then-filter,broad untracked inventory or old scan rerun. Disclose false admissions,coarse omissions,versions/read extents,truncation recovery,late reads and incomplete transitive ancestry. Seal YOUR own fresh exact selection ONCE with detached FINAL/MANIFEST/outside REPORT anchors,a read-only explicit-anchor verifier and proportionate tiny COPIED own-text controls. No inherited manifest over fewer files. Artifact checks are not math gates. No nested agents,shared/git writes,public/browser actions or downstream formal/manuscript/release work. Parent alone commissions independent correctness and separate actual-primary substantial-contribution reviews of a viable full author proof.

'''
extra = '\nFurther prospective literal twins and opaque aliases observed in the completed preceding round:\n*arithmetic*162ab* *arithmetic*r162ab* *i137_crystalline_coherence* *iteration217-priority-stop-request*\n\n'
brief = (prefix + previous + section + isolation + extra + marker.decode()).encode() + standing
old_guards = {p for p in re.findall(r'\*[^\s,;()]*\*', old) if p not in {'*', '**'}}
new_guards = {p for p in re.findall(r'\*[^\s,;()]*\*', brief.decode()) if p not in {'*', '**'}}
assert old_guards <= new_guards
assert brief.split(marker,1)[1] == standing
brief_path.write_bytes(brief)
dump(N / 'brief-preparation.json', dict(brief=brief_path.relative_to(P).as_posix(), bytes=len(brief), sha256=sha(brief), standing_bytes_preserved=5570, all_previous_literal_guards_retained=True, source='093', catalogue_extent=[155355,156394], source094_body_not_selected=True, canonical_blobs=13, canonical_entries_including_roots=17, completed_direct_inputs=5, parent_source_body_read=False, publication='STOPPED'))
dump(N / 'private/canonical-selection.json', selected)
print(json.dumps(dict(brief_bytes=len(brief), brief_sha256=sha(brief), checked_foreign_original_briefs=len(checks), canonical_blobs=13, parent_root=N.relative_to(P).as_posix())))
