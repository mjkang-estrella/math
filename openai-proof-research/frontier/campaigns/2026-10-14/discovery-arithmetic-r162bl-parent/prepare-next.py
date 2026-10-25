#!/usr/bin/env python3
"""Prepare a distinct Source146 research round after skipping paid Source145."""
from pathlib import Path
import fnmatch, hashlib, json, re, subprocess
P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'; D = Path(__file__).resolve().parent
N = B / 'discovery-arithmetic-r162bm-parent'; R = B / 'fresh-arithmetic-discovery-r162bm'
BP = B / 'expanded-target-2026-10-17/fresh-arithmetic-r162bm-brief.txt'
def sha(a): return hashlib.sha256(a).hexdigest()
def dump(p, x): p.write_text(json.dumps(x, ensure_ascii=False, indent=2) + '\n')
def git(*args): return subprocess.check_output(['git', *args], cwd=P)
def rules(s): return {z for z in re.findall(r'\*[^\s,;()]*\*', s) if z not in {'*', '**'}}

head = git('rev-parse', 'HEAD').decode().strip()
t = json.loads(git('show', head + ':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'))
assert t['newAccepted'] == 19 and t['gpt_subagent_preferences']['serviceTier'] == 'default'
assert not git('diff', '--cached', '--name-only').strip()
names = [x.relative_to(P).as_posix() for x in [N, R, BP]]; checks = []; legacy = []
for i, x in enumerate(t['tasks']):
    if i == 815 or x.get('status') not in {'running', 'queued', 'waiting'}: continue
    if not x.get('brief'):
        assert 'nativeTaskName' in x and 'taskId' not in x
        legacy.append(i); continue
    a = (P / x['brief']).read_bytes()
    assert not x.get('brief_sha256') or sha(a) == x['brief_sha256']
    matches = {n: sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(), z.casefold())) for n in names}
    assert all(matches.values())
    checks.append(dict(task_index=i, original_brief=x['brief'], sha256=sha(a), matches=matches))
guard = dict(head=head, before_creation=True, namespaces=names, original_foreign_brief_guard_checks=checks, legacy_native_without_original_brief=legacy, foreign_live_queries=False, recorded_status_not_live_liveness=True)
dump(D / 'integration-guard.json', guard)
assert not N.exists() and not R.exists() and not BP.exists()

original = (B / 'expanded-target-2026-10-17/fresh-arithmetic-r162bl-brief.txt').read_bytes()
assert len(original) == 119244 and sha(original) == '740e4cb4095f0260abdfd039a5d2edb5c6c58964c8ae7e300df8aa5026abe840'
old = original.decode(); marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing = original.split(marker, 1)[1]; assert len(standing) == 5570
prefix = old[:old.index('Read the COMPLETE actual Source144')]
prefix = prefix.replace('Arithmetic discovery r162bl — confirmed smooth-simple-Lebesgue-spectrum operative-proof discovery.', 'Arithmetic discovery r162bm — confirmed standard-map metric-entropy operative-proof discovery.', 1)
prefix = prefix.replace('fresh-arithmetic-discovery-r162bl/', 'fresh-arithmetic-discovery-r162bm/', 1).replace('FRESH DISTINCT Source144', 'FRESH DISTINCT Source146', 1).replace('Own r162bl I/O', 'Own r162bm I/O', 1)
instructions = '''Read the COMPLETE actual Source146 operative proof,actual build/paper.tex wrapper,ALL mathematical includes,figure,references and strongest relevant primary/companion proofs BEFORE selecting ONE additional full theorem. The ENTIRE stipulated result is ALREADY PAID:the ORIGINAL standard sine map on the two-dimensional torus has positive metric entropy for normalized AREA for EVERY sufficiently large positive parameter,a full parameter tail. Do not audit source truth or nominate this result. Read and credit ALL stronger actual geometric,dynamical,quantitative,measure and parameter operations,not just the catalogue headline.

Track the SAME original map,parameter,normalized area,critical strips,return/inducing structures and limiting construction throughout. Positive topological entropy,a hyperbolic set,existence of some invariant measure,positive Lyapunov exponent for selected points,or a positive-measure parameter subset does not replace a full area-entropy assertion. Ergodicity,mixing,full-measure exponents,quantitative entropy/asymptotic rates,robustness and changed forcing functions require their actual additional interfaces. Do not silently upgrade source constants to uniform values,change the map/family,or replace physical recurrence and transport bounds by independent models. Classical Pesin/ergodic/inducing/parameter transfers are paid at their actual hypotheses;read operative primaries before calling compatibility new.

Perform sustained mathematical derivation after complete source and strongest relevant primary reading. Choose ONE viable genuinely additional operation;freeze every hypothesis,quantifier,map/measure/parameter convention,constant and conclusion only when a complete nonroutine proof is viable,then prove the ENTIRE scope. Parent alone commissions independent adversarial correctness and separate actual-primary substantial-contribution reviews. No self-gates/count,desired-grade retry,narrowing,renaming or reopening older full targets. This standard-map family is distinct from smooth-simple-spectrum construction;all earlier ergodic,entropy,spectral and arithmetic scopes retain dispositions. No history-clearance or never-investigated claim.

R162BL is archived PREFREEZE/no nominee;no theorem or diagnostic frozen. Entire Source144 and its fully read Source145 multiple-mixing companion,stronger actual ordered-array/saturation,conditional-locality,both rectangle identities,dense-range polar,exact-line/measurable descent,counting-lift,arbitrary-coupling cancellation and endomorphism/flow operations are PAID. SAME-map all-point/all-positive-order subexponential derivative growth and zero topological entropy close through the ordinary finite-iterate diagonal. Smooth real cyclic observables dense in the smooth topology and bounded finite-stage exact whitening (including spectral-zero fill) are also CLOSED source/classical comparisons. Physical infinite-stage whitening regularity remains unproved/unfrozen;L2 convergence plus separately finite bounds cannot supply uniform norm control. Joint angular/spare-coordinate fourth-moment resonances remain in the exact formula;unitary-to-spatial,multiplicative-algebra and finite-window-to-all-time shortcuts are invalid. No universal impossibility claim.

Both canonical proofs22 texts248343 bytes fully read,24 blobs31 entries authenticated;2 PDFs authentication-only. Three primary PDFs66 distinct touched pages,some partial,exactly one full26-page paper,3 renders;late recoveries,404/non-PDF failures,incidental unused snippets and incomplete ancestry disclosed. Five completed exceptions,history0. Parent/bundled artifact MATCH64 payloads3951719 bytes,66 files,11 directories;all seals unchanged. Initial author records captured permissions only;later full modes and separate parent pre-dispatch full modes match without retroactive initial observation. No gates/count. Source145 is ALREADY PAID and was skipped deliberately,not renamed as fresh research.

'''
older = old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')]
historical = old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation = old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
nav = json.loads((D / 'private/intake/next-source-navigation.json').read_bytes())
sel = json.loads((D / 'private/intake/Source146-selection.json').read_bytes())
assert sel['catalogue_extent'] == [241294, 242223] and len(sel['folders']) == 1 and len(sel['entries']) == 16
blobs = [e for e in sel['entries'] if e['type'] == 'blob']
assert len(blobs) == 12 and sum(e['size'] for e in blobs if not e['path'].endswith('.pdf')) == 145989
wrapper = next(e for e in blobs if e['path'] == sel['folders'][0] + '/build/paper.tex')
assert wrapper['size'] == 2705 and wrapper['sha'] == 'd685d6f3d32384a77d2de437b5660d2846015574'
direct = [D / 'assessment.md', B / 'fresh-arithmetic-discovery-r162bl/private/COMPARISON.md', B / 'fresh-arithmetic-discovery-r162bl/private/WORKING.md', B / 'fresh-arithmetic-discovery-r162bl/private/READING-LIMITS.md', B / 'fresh-arithmetic-discovery-r162bl/FINAL.md']
inputs = []
for f in direct:
    a = f.read_bytes(); inputs.append(dict(path=f.relative_to(P).as_posix(), bytes=len(a), sha256=sha(a), mode=f.stat().st_mode))
section = '''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[241294,242223),EXACT Source146. Parent used ONE bounded14000-byte window[240464,254464),decoding ONLY first TWO numeric-bold TITLE STRINGS145/146 and their TWO bodies;third heading147 used ONLY as byte boundary,not semantically read. Source145 was skipped because it was ALREADY fully read and paid as r162bl's companion. TWO family-body screens,ONE selection. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay. Navigation is not exhaustive clearance.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
''' + sel['folders'][0] + '\n' + wrapper['path'] + '; bytes2705; Git blob' + wrapper['sha'] + '''.
Combined:12 blobs/16 entries including root,11 textual objects145989 bytes and one compiled PDF. Read ALL operative texts in full,including actual build/paper.tex,all seven sections,bridge-sweep figure and references. Authenticate exact bytes/metadata;do not guess a wrapper or substitute metadata/abstract for proof. Parent operative-source reading:NONE. lean/docs/146.md,if present,is scoped comparator navigation only;no downstream formalization or end-to-end verification inference.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
''' + '\n'.join(e['path'] for e in inputs) + '''
These narrow exceptions authorize NO containing namespace,linked source/primary bundle,older exception,review,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY,not this family's operative proof. Protected bodies AND named metadata stay PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and bytes/body access at EVERY depth. Query genuine authored standard-map/area-entropy,critical-recurrence,inducing,parameter-uniform transport,entropy/physical-Lyapunov or related operative mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through equal/higher headings;record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim. Actual overlap comparisons precede novelty claims.

Seal once with explicit detached anchors and a read-only verifier. BEFORE sealing,sort records if required;assert uniqueness and preflight SAME final verifier logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,modes and copies. Tiny copied controls suffice;do not trade sustained mathematics for administrative suites. Distinguish artifact checks from mathematical gates;report any failure honestly. Record full st_mode at initial capture when needed;permissions-only values must remain qualified.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
extra = '\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162bm* *arithmetic*r162bm*\n\n'
brief = (prefix + instructions + older + section + historical + isolation + extra + marker.decode()).encode() + standing
assert rules(old) <= rules(brief.decode())
assert {'*arithmetic*162bm*', '*arithmetic*r162bm*', '*structural*r220*'} <= rules(brief.decode())
assert brief.split(marker, 1)[1] == standing
assert brief.decode().splitlines()[1] == 'Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bm/.'
assert len(brief.decode()) < 120000, len(brief.decode())
assert 'serviceTier default.' in brief.decode() and 'come back to STANDARD speed' in brief.decode()
N.mkdir(mode=0o700); R.mkdir(mode=0o700); (N / 'private').mkdir(mode=0o700)
dump(N / 'prospective-isolation.json', guard)
for name, obj in [('completed-direct-inputs.json', inputs), ('canonical-selection.json', sel), ('catalogue-navigation.json', nav)]:
    dump(N / 'private' / name, obj); (N / 'private' / name).chmod(0o600)
BP.write_bytes(brief)
prep = dict(brief=BP.relative_to(P).as_posix(), bytes=len(brief), characters=len(brief.decode()), sha256=sha(brief), standing_bytes_preserved=5570, all_previous_literal_guards_retained=True, all_extra_guard_literals_verified=True, distinct_family=True, source=146, catalogue_extent=[241294,242223], canonical_folders=1, canonical_blobs=12, canonical_entries_including_roots=16, canonical_text_objects=11, canonical_text_bytes=145989, serviceTier='default', vendor_runtime_blobs=0, completed_direct_inputs=5, parent_source_body_read=False, new_family_screens=2, skipped_paid_source=145, title_navigation_windows=1, all_older_scopes_preserved=True, publication='STOPPED')
dump(N / 'brief-preparation.json', prep)
print(json.dumps(prep))
