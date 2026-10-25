#!/usr/bin/env python3
"""Prepare distinct Source139 log-concave sampling research and all guards."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162bg-parent';R=B/'fresh-arithmetic-discovery-r162bg';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162bg-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
head=git('rev-parse','HEAD').decode().strip();t=json.loads(git('show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'))
assert t['newAccepted']==19 and not git('diff','--cached','--name-only').strip()
names=[x.relative_to(P).as_posix() for x in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==800 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values())
 checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,foreign_live_queries=False,recorded_status_not_live_liveness=True)
dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists();N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(N/'prospective-isolation.json',guard)
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bf-brief.txt').read_bytes();assert len(original)==111166 and sha(original)=='c063c91ed2c72aa794650134190df4ec87e5223e91a35e58fb6e8f49ca217151'
old=original.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=original.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read the COMPLETE actual Source138')].replace('Arithmetic discovery r162bf — confirmed worst-case-Subset-Sum operative-proof discovery.','Arithmetic discovery r162bg — confirmed log-concave-sampling operative-proof discovery.',1).replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bf/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bg/.',1).replace('FRESH DISTINCT Source138','FRESH DISTINCT Source139',1).replace('Own r162bf I/O','Own r162bg I/O',1)
instructions='''Read the COMPLETE actual Source139 operative proof,actual wrapper,ALL includes,figures,bibliography and strongest primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE stipulated sampler is ALREADY PAID:for EVERY fixed epsilon>0,a uniform randomized algorithm uses at most C_epsilon d^epsilon exact value-and-gradient queries on EVERY execution for EVERY C^2 potential V on R^d with supplied minimizer and I<=Hessian V<=2I,and output TV distance<=1/10 from the normalized Gibbs law. Computation between queries is UNRESTRICTED. The Omega(log d) lower bound for arbitrary randomized adaptive algorithms and zero optimal power-law exponent are also PAID. Catalogue headlines are NOT the boundary;read and credit ALL stronger actual centering,divergence,jet,sampling,numerical,implementation and lower-bound operations. Do not audit or nominate source theorems.

Track the SAME potential,oracle transcript,center/reference,randomness and output law through every proposed composition. Preserve exact value+gradient versus Hessian/normalizer/sampling/integration oracles;known minimizer versus unknown or approximate center;C^2 and global matrix bounds;dimension and fixed-epsilon quantifiers;every-execution versus expectation;TV versus weaker metrics;arbitrary computation versus finite-bit runtime or workspace. Charge queries,adaptivity,preprocessing,termination,precision/noise/randomness and restart probabilities in ANY stronger model claimed. Do not infer polynomial runtime from query count or finite precision from exact real answers. Standard affine/temperature rescaling,product/tensor,change of variables,centering,accuracy amplification,warm-start and classical sampler/oracle reductions are paid where ACTUAL hypotheses hold. Read stronger actual primary interfaces before declaring a missing operation new.

Perform sustained mathematical derivation after complete source and strongest relevant primary reading. Choose ONE viable genuinely additional operation;freeze every hypothesis,quantifier,constant,oracle/model,accuracy,resource and conclusion only when a full nonroutine proof is viable,then prove ENTIRE scope. Parent alone commissions independent adversarial correctness and separate actual-primary substantial-contribution reviews. No self-gates/count,desired-grade retry,narrowing,renaming or reopening older targets. This is a distinct sampling family,not a replacement for unchanged full entropy-overlap C or modified log-Sobolev/posterior-budget targets. Those remain unproved with unchanged scopes. No history-clearance or never-investigated claim.

R162BF is archived PREFREEZE/no nominee;no theorem or diagnostic frozen. BOTH entire actual Source138 algorithms and stronger operations are paid,including every-fixed-polynomial-bit uniformity,original indexed repetitions,isolation/moduli/tables/phases/global multiplicities/coverage and overflow events. Ordinary adaptive decision-to-verified-witness,model and output-sensitive search comparisons are paid. Fast checksum decision alone is not one-sided verified witness output. Two storage concerns CLOSED:checksum prefix-count array replaced by two-pass replay and bounded finite-bit sorted-rank stream preserving the original occurrence law;alias SET replaced by small-mixer canonical dictionaries in poly(n+b)2^(.08505n) work/storage with SAME-seed replay. Alias extraction/caps precede independent phase draws;actual reduced/unreduced tests remain. Large sorted incidence and filtered-record arrays remain. Primary heavy-weight majority recovery/exact-mask regeneration is credited.

Unproved/UNFROZEN sufficient route:ONE common smaller-memory generator/organization for actual checksum incidences AND actual alias reduced/unreduced forbidden-interval relation,preserving same seeds/phases/multiplicities,caps/aborts/checks,with every preprocessing/sort/replay/precision/randomness cost in ordinary O(2^(.49n)) under EVERY fixed polynomial input-bit bound. Separate algorithms' resources do not combine for free. Exact product-sampler row/column covariance and stronger prefix-filter modular-orbit autocorrelation sums are retained. Independent-phase moments do not supply that same-table orbit estimate. Failed overflow/head-count/replay bounds refute no universal algorithm. No simultaneous-resource theorem,lower bound,counting/sampling/arbitrary-bit substitute or frozen diagnostic is nominated.

All22 canonical texts244917 bytes read;24 blobs/29 entries authenticated;both wrappers/all includes/figure/numerical appendix/bibliographies read,two PDFs authentication only. Eight primary PDFs176 distinct semantically read pages,five full extracts118 pages,four rendered checks;versions,selected RW/LSF/KLM intervals,late reads,imperfect OCR,truncation recoveries and incomplete ancestry disclosed. Five completed exceptions,zero optional history traversal,no full balanced source algorithm/numerical optimization/certificate audit run. Original verifier plus parent authentication MATCH67 payload records includingFINAL8961687 bytes,69 files,12 directories;all5 initial originals/copies/full modes unchanged. Three wrong anchors rejected,restored tiny fixture MATCH. Artifact checks only,no mathematical gates/count. All older scopes/dispositions preserved.

'''
older=old[old.index('R162BE is archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
nav=json.loads((D/'private/intake/next-source-navigation.json').read_text());sel=json.loads((D/'private/intake/Source139-selection.json').read_text())
assert sel['catalogue_extent']==[229493,230880] and len(sel['folders'])==1 and len(sel['entries'])==19
blobs=[e for e in sel['entries'] if e['type']=='blob'];assert len(blobs)==15 and sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'))==198440
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162bf/private/DERIVATIONS.md',B/'fresh-arithmetic-discovery-r162bf/private/WORKING.md',B/'fresh-arithmetic-discovery-r162bf/private/READING-LIMITS.md',B/'fresh-arithmetic-discovery-r162bf/FINAL.md'];inputs=[]
for f in direct:
 a=f.read_bytes();inputs.append(dict(path=f.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=f.stat().st_mode))
dump(N/'private/completed-direct-inputs.json',inputs);dump(N/'private/canonical-selection.json',sel);dump(N/'private/catalogue-navigation.json',nav)
for n in ['completed-direct-inputs.json','canonical-selection.json','catalogue-navigation.json']:(N/'private'/n).chmod(0o600)
section='Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[229493,230880),EXACT Source139. Parent used ONE bounded14000-byte window[229493,243493),decoding ONLY FIRST TWO numeric-bold TITLE STRINGS139/140 and ONLY139 BODY. Source140 body/remainder NOT decoded;third heading ONLY byte boundary,not title/body. ONE family BODY screened. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay. Navigation is not exhaustive clearance.\n\nConfirmed canonical folder and ACTUAL wrapper from complete-tree metadata:\n'
for folder in sel['folders']:
 candidates=[e for e in blobs if e['path']==folder+'/build/main.tex'];assert len(candidates)==1;w=candidates[0]
 section+=folder+f"\nACTUAL wrapper:{w['path']} bytes{w['size']};Git blob{w['sha']}.\n"
section+='There are15 blobs/19 entries including root:14 textual objects198440 bytes and one compiled PDF. Authenticate exact bytes/metadata;read ALL operative text,actual build/main.tex wrapper,all9 section includes,2 figure TeX files and references. Do not guess build/source/main.tex. ALL stronger actual centering/divergence/jet/sampling/numerical/implementation/lower-bound operations are paid. Parent operative-source reading:NONE. lean/docs/139.md,if present,is scoped comparator navigation only;no downstream formal work or end-to-end formalization inference.\n\nRead these FIVE exact COMPLETED originals(project-relative POSIX):\n'+'\n'.join(e['path'] for e in inputs)
section+='''
These narrow exceptions authorize NO containing namespace,linked source/primary bundle,older exception,review,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY,not this family's operative proof. Protected bodies AND named metadata stay PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and bytes/body access at EVERY depth. Query genuine authored log-concave sampling,exact first-order oracle,query complexity,centering/divergence/jet/implementation,accuracy/precision/noise,adaptive lower-bound and full joint-transcript mechanisms as relevant. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through equal/higher headings;record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim. Actual overlap comparisons precede novelty claims.

Seal once with explicit detached anchors and a read-only verifier. BEFORE sealing,sort records if required;assert uniqueness and preflight SAME final verifier logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,modes and copies. Tiny copied controls suffice;do not trade sustained mathematics for administrative suites. Distinguish artifact checks from mathematical gates;report any failure honestly.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
suffix=R.name.rsplit('-',1)[1]
extra=f'\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*{suffix[1:]}* *arithmetic*{suffix}*\n\n'
brief=(prefix+instructions+older+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {f'*arithmetic*{suffix[1:]}*',f'*arithmetic*{suffix}*','*structural*r220*'}<=rules(brief.decode())
assert brief.split(marker,1)[1]==standing and brief.decode().splitlines()[1]=='Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162bg/.'
BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,distinct_family=True,source=139,catalogue_extent=[229493,230880],canonical_folders=1,canonical_blobs=15,canonical_entries_including_roots=19,nonvendor_texts=14,canonical_text_bytes=198440,vendor_runtime_blobs=0,completed_direct_inputs=5,parent_source_body_read=False,new_family_screens=1,source140_body_not_decoded=True,title_navigation_windows=1,all_older_scopes_preserved=True,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=15,canonical_entries=19,all_guards_retained=True,distinct_family=True)))
