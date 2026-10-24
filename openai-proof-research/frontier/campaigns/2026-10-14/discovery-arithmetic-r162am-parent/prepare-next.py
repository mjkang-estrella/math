#!/usr/bin/env python3
"""Prepare Source110 discovery while preserving all old scopes and guards."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162an-parent';R=B/'fresh-arithmetic-discovery-r162an'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162an-brief.txt'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
head=git('rev-parse','HEAD').decode().strip();raw_t=git('show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json');raw_j=git('show',head+':openai-proof-research/frontier/NEW-TEN-2026-10-14.md')
assert (B/'tasks.json').read_bytes()==raw_t and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()==raw_j
assert not git('diff','--cached','--name-only').strip();t=json.loads(raw_t);assert t['newAccepted']==19
names=[x.relative_to(P).as_posix() for x in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
    if i==738 or x.get('status') not in {'running','queued','waiting'}:continue
    if not x.get('brief'):
        assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
    raw=(P/x['brief']).read_bytes();matches={n:[z for z in sorted(rules(raw.decode())) if fnmatch.fnmatchcase(n.casefold(),z.casefold())] for n in names}
    assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(raw),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,foreign_live_queries=False,recorded_status_not_live_liveness=True)
dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists()
N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162am-brief.txt').read_bytes()
assert sha(original)=='c3995bc602ff985ddc1fa99ec72ae08d85b9c01ab0a3079dbae9c49d8954a85b'
old=original.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=original.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read the COMPLETE actual Source109')]
prefix=prefix.replace('Arithmetic discovery r162am — confirmed integer-multiplication operative-proof discovery.','Arithmetic discovery r162an — confirmed randomized k-server operative-proof discovery.',1)
prefix=prefix.replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162am/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162an/.',1)
prefix=prefix.replace('FRESH DISTINCT Source109','FRESH DISTINCT Source110',1).replace('Own r162am I/O','Own r162an I/O',1)
instructions='''Read the COMPLETE actual Source110 existence AND uniform-computation constructions and strongest operative primary/companion interfaces BEFORE selecting a full result. The ENTIRE stipulated randomized k-server theorem is ALREADY PAID:O(log^2(k+1)) competitiveness on EVERY metric space against oblivious finite request sequences,ONE policy serving ALL those sequences for each metric/initial configuration,including infinite unbounded metrics,and the stronger no-additive-term conclusion for distinct initial positions at its actual hypotheses. The companion supplies a UNIFORM finite-rational-metric implementation with polynomial preprocessing and per-request BIT cost polynomial in complete input length and log(t+1),with a finite instance-dependent additive movement constant that may be enormous. Read actual stronger proofs instead of treating headlines as the full paid interface. Do not audit upstream truth,nominate either theorem itself,a routine existence-to-implementation transfer already provided,or a familiar application already paid by compatible source/classical operations.

Track metric domains,server count,initial collisions,ONE-policy/all-sequence quantifiers,oblivious versus adaptive adversaries,what randomness the adversary sees,expectation/tails/pathwise guarantees,ratio and additive term,finite versus infinite/unbounded metrics,explicit rational encodings,uniform construction and all randomness/preprocessing/per-request/movement/bit costs. A huge finite additive constant is not absent,not a polynomial bound and not an unpaid gap in the stated source theorem. Changing the adversary,resource model,metric oracle or information pattern requires an actual full proof. Do not infer substantial contribution from a failed naive composition or an unproved robustness bridge. Choose ONE promising full operation only AFTER the strongest integrated source/actual-primary comparison,then do sustained mathematics. Freeze every quantifier,hypothesis,constant and conclusion only when a viable full theorem emerges,before extended proof drafting. Parent alone commissions independent correctness and substantial-contribution gates. No restricted/renamed substitute or desired-grade retry for an older full target.

R162AM is archived PREFREEZE/no nominee. Preserve its FULL unproved diagnostic:ONE deterministic fixed finite-alphabet machine with a FIXED finite number of one-dimensional tapes and ONE numerical C computes,for EVERY prime p and n>=1,the ordinary product of two explicit degree<n polynomials over F_p,outputting ALL2n-1 canonical coefficients in increasing order,in C L log2(L+2)^(1-2^-182) bit steps. L counts the COMPLETE explicit binary encoding,including n,p,fixed-width coefficient fields and delimiters. Primality is a promise;characteristic2,zero coefficients,all lengths,precomputation,arithmetic,movement,reductions and output are included. Unequal lengths have only the documented maximum-padding/combined-input comparison,no sharper unbalanced bound. Neither this diagnostic nor its negation is proved. No theorem was frozen and no gate/count assigned.

Its source integer multiplier,stronger division/square-root/transposition/grouped-rectangle operations,the complete explicit complex DFT construction,and compatible primary reductions are already paid. Retained author work includes lift heights/carries,the paid uneven-chunk correction,the normalized cyclotomic recursion budget and an exact simultaneous controlled-swap identity over rings with invertible2. The large-characteristic lift is paid;it does not replace the full diagnostic. One exact simultaneous all-characteristic transform compiler on the SAME cyclotomic decomposition,including scalar widths,roots/constants,residual products,layouts and every tape/bit cost,is a sufficient unpaid route,not a necessary/exhaustive route. Other algorithms may bypass it. No failed specialization or induction is a lower bound. Source109 and explicit DFT text fully read;further general tensor text only5 of11 authenticated objects read completely,transitive primary ancestry incomplete,no optional history traversal. Do not reopen that diagnostic or a weaker substitute in this k-server family.

'''
older=old[old.index('The prior Source107 square/rectangular interfaces'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
nav=json.loads((D/'private/intake/next-source-navigation.json').read_text());selected=json.loads((D/'private/intake/Source110-selection.json').read_text())
assert len(selected['folders'])==2 and len(selected['entries'])==42
blobs=[x for x in selected['entries'] if x['type']=='blob'];assert len(blobs)==31
wrappers=[next(x for x in blobs if x['path']==f+'/build/source/main.tex') for f in selected['folders']]
assert [x['size'] for x in wrappers]==[1179,2003]
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162am/private/MATH.md',B/'fresh-arithmetic-discovery-r162am/private/SOURCE-COMPARISON.md',B/'fresh-arithmetic-discovery-r162am/private/READING-LIMITS.md',B/'fresh-arithmetic-discovery-r162am/private/FINAL.md']
inputs=[]
for f in direct:
    raw=f.read_bytes();inputs.append(dict(path=f.relative_to(P).as_posix(),bytes=len(raw),sha256=sha(raw),mode=f.stat().st_mode))
dump(N/'private/completed-direct-inputs.json',inputs);dump(N/'private/canonical-selection.json',selected);dump(N/'private/catalogue-navigation.json',nav)
section='''Catalogue access,if needed: ONLY binary seek/read sources/CONTENTS.md[182733,184788),EXACT Source110. Parent used ONE bounded14000-byte window at182733,decoded only FIRST TWO new-family numeric-bold TITLE STRINGS110/111,then selected ONLY110 body. Source111 body was NOT decoded. Exact known prior-companion link metadata was checked for skipping;there were NO such matches or skipped sources. No child title locator,extra family/catalogue screen,whole-catalogue read,ancestor hunt or old scan replay. ONE new family was screened. Metadata is navigation/authentication,not semantic proof reading or an exhaustive-clearance certificate.

Confirmed folders and ACTUAL wrappers follow. There are31 blobs/42 complete-tree entries including roots. Parent source-proof reading:NONE. Fetch exact pinned raw paths and follow actual textual includes;do not guess root main.tex or build/main.tex. Authenticate selected objects,read complete operative proofs,and distinguish PDF/metadata authentication from semantic reading and actual rendered-page inspection. BOTH source constructions are stipulated TRUE at the pin,including stronger internal operations.
'''
for f,w in zip(selected['folders'],wrappers):section+=f'\n{f}\nACTUAL WRAPPER {w["path"]}\nbytes{w["size"]};Git blob{w["sha"]}.\n'
section+='\nRead these FIVE exact COMPLETED originals(project-relative POSIX):\n'+'\n'.join(x['path'] for x in inputs)
section+='''
These narrow exceptions authorize NO containing namespace,linked source/primary bundle,older direct exception,role/status/brief/activity alias or other review. No permission in an older file propagates. They are prior-scope/payment/reading-limit context ONLY,not this family's operative source reading. Protected bodies AND their named metadata remain PRIVATE/local under original rights;copies/excerpts stay only in your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized for this distinct family. Evaluate EVERY inherited literal wildcard/substring on the full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and byte/body access at EVERY depth. Query genuine authored k-server,online metric algorithms,randomized competitiveness,adversaries,uniform policy construction,rounding and resource-augmentation mechanisms as relevant. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through equal/higher headings;record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If no optional scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162an* *arithmetic*r162an*\n\n'
brief=(prefix+instructions+older+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {'*arithmetic*162an*','*arithmetic*r162an*'}<=rules(brief.decode())
assert brief.split(marker,1)[1]==standing
assert brief.decode().splitlines()[:2]==['Arithmetic discovery r162an — confirmed randomized k-server operative-proof discovery.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162an/.']
BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,distinct_family=True,source=110,catalogue_extent=[182733,184788],canonical_folders=2,canonical_blobs=31,canonical_entries_including_roots=42,completed_direct_inputs=5,parent_source_body_read=False,new_family_screens=1,next_source111_body_not_decoded=True,full_uniform_prime_field_diagnostic_preserved=True,all_older_scopes_preserved=True,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=31,canonical_entries=42,both_new_literal_twins_verified=True,distinct_family=True)))
