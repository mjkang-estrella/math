#!/usr/bin/env python3
"""Prepare distinct Source109 work with original guards and all earlier scopes."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162am-parent';R=B/'fresh-arithmetic-discovery-r162am'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162am-brief.txt'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
head=git('rev-parse','HEAD').decode().strip();raw_t=git('show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json');raw_j=git('show',head+':openai-proof-research/frontier/NEW-TEN-2026-10-14.md')
assert (B/'tasks.json').read_bytes()==raw_t and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()==raw_j
assert not git('diff','--cached','--name-only').strip();t=json.loads(raw_t);assert t['newAccepted']==19
names=[x.relative_to(P).as_posix() for x in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
    if i==737 or x.get('status') not in {'running','queued','waiting'}:continue
    if not x.get('brief'):
        assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
    raw=(P/x['brief']).read_bytes();matches={n:[z for z in sorted(rules(raw.decode())) if fnmatch.fnmatchcase(n.casefold(),z.casefold())] for n in names}
    assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(raw),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,foreign_live_queries=False,recorded_status_not_live_liveness=True)
dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists()
N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162al-brief.txt').read_bytes()
assert sha(original)=='375a47dd89ea85aca3bfe267e2041dda3941b33f704866d71bf6dc124e9afa71'
old=original.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=original.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read the COMPLETE actual Source107')]
prefix=prefix.replace('Arithmetic discovery r162al — confirmed matrix-multiplication operative-proof discovery.','Arithmetic discovery r162am — confirmed integer-multiplication operative-proof discovery.',1)
prefix=prefix.replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162al/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162am/.',1)
prefix=prefix.replace('FRESH DISTINCT Source107','FRESH DISTINCT Source109',1).replace('Own r162al I/O','Own r162am I/O',1)
instructions='''Read the COMPLETE actual Source109 theorem/proof construction and strongest operative primary/companion interfaces BEFORE selecting a full result. The ENTIRE stipulated algorithm is ALREADY PAID:exact multiplication of two n-bit integers at EVERY input length in deterministic worst-case O(n(log n)^(1-kappa)),kappa=2^(-182),on ONE fixed finite-alphabet Turing machine with a FIXED finite number of one-dimensional tapes. Read the actual proof,its uniform construction,all stronger operations and the precise small-input conventions. Do not audit upstream truth,rerun its certificates as new evidence,or nominate the below-nlogn statement itself,its conjecture consequence,ordinary arithmetic applications or routine substitution of this M(n) into known reductions.

Track the actual machine/tape model,all-length uniformity,worst-case versus amortized/expected costs,balanced/unbalanced lengths,exact signed output,coefficient heights and carries,precision and error,layout/permutations/addressing,precomputation/tables/compiler description,space,constants and every input/output/bit cost. No unit-cost RAM,arbitrary field operation,unbounded word,nonuniform advice,uncharged preprocessing or concurrent tape is free. Stronger operative source and primary constructions may already pay an apparent gap. A failed naive transfer or unproved uniformity bridge is not evidence of a substantial result. Choose ONE promising full operation AFTER the strongest integrated source/actual-primary comparison and do sustained mathematics. Freeze all hypotheses,quantifiers,constants and the conclusion only when a viable full theorem emerges,before extended proof drafting. Parent alone commissions independent correctness and substantial-contribution gates. No restricted or renamed replacement or desired-grade retry for any old full scope.

The prior Source107 square/rectangular interfaces remain fully paid:omega_C<=9/4,characteristic-zero dual alpha>0.465 and omega(1,0.709,1)<2.092,companion square<2.258 with its stated finite characteristic exceptions,and every-fixed-field square<2.371054886006746,all at their actual stronger proof scopes. These are context,not permission to reopen the old canonical/primary namespaces.

R162AL is archived PREFREEZE/no nominee. Its exact scalar-interface investigation is closed at the author-comparison level:positive symmetric P on positive integer pairs,P(1,b)=b,separate discrete concavity and all P(a,3h+a-1)>=3P(a,h) admit the pointwise least Q(a,b)=ell_min(a,b)[max(a,b)+(min(a,b)-1)/2],ell_1=1,ell_(a+1)/ell_a=(3a+1)/(3a). Q has diagonal Theta(a^(4/3)) and survives every analyzed unequal odd-sector packing/common entropy extension and the rank-upper relaxation. No actual tensor character realizing Q or true exponent lower bound is claimed. Fixed-field9/4 arithmetic and fixed-epsilon exact integer/residue bit-cost transfers are already credited compatible source/classical compositions,including whole-recursion fixed-extension simulation and layer-denominator/coefficient/output costs. No nonroutine operation was closed. An epsilon-free construction-rate direction was considered but NOT selected,frozen,proved or asserted necessary. Do not turn that unselected direction,method limit or ordinary bit transfer into a nominee. Canonical construction reading complete,transitive primary ancestry incomplete,no optional original-history traversal. No gates/count.

'''
older=old[old.index('R162AK is archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
selected=json.loads((D/'private/intake/Source109-selection.json').read_text());nav=json.loads((D/'private/intake/next-source-navigation.json').read_text())
assert len(selected['folders'])==1 and len(selected['entries'])==22
blobs=[x for x in selected['entries'] if x['type']=='blob'];assert len(blobs)==18
folder=selected['folders'][0];wrapper=next(x for x in blobs if x['path']==folder+'/build/main.tex')
assert wrapper['size']==1882 and wrapper['sha']=='0b11a3feb14714253c1ca06ee561a31dd2fe8662'
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162al/private/MATH.md',B/'fresh-arithmetic-discovery-r162al/private/READING-LIMITS.md',B/'fresh-arithmetic-discovery-r162ak/private/PREFREEZE-SCOPE.md',B/'discovery-arithmetic-r162aj-parent/proof-assessment.md']
inputs=[]
for f in direct:
    raw=f.read_bytes();inputs.append(dict(path=f.relative_to(P).as_posix(),bytes=len(raw),sha256=sha(raw),mode=f.stat().st_mode))
dump(N/'private/completed-direct-inputs.json',inputs);dump(N/'private/canonical-selection.json',selected);dump(N/'private/catalogue-navigation.json',nav)
section=f'''Catalogue access,if needed: ONLY binary seek/read sources/CONTENTS.md[181743,182733),EXACT Source109. Parent used ONE bounded14000-byte window at180526 and decoded only FIRST TWO numeric-bold TITLE STRINGS108/109. Source108 description was the first family screen,then skipped because the historical USER handoff already identifies Structural174 border permanent-determinant work with an unpaid construction;NO protected historical body was opened. Source109 description is the second/final family screen. The SAME window was reread to recover its exact boundary;heading110 supplied ONLY a byte position,no title/body decode. No child title locator,extra family/catalogue screen,whole catalogue read,ancestor hunt or old scan replay. This is bounded navigation,not exhaustive clearance.

Confirmed canonical folder:
{folder}
ACTUAL wrapper from complete-tree metadata:
{wrapper['path']}
bytes1882;Git blob0b11a3feb14714253c1ca06ee561a31dd2fe8662.
There are18 blobs/22 entries including root. Parent operative source-proof reading:NONE. Fetch pinned raw paths under this exact folder and follow the actual textual includes. Do not guess root main.tex or invent build/source/. Authenticate selected objects,read the complete operative proofs,and distinguish metadata/PDF authentication from semantic or rendered-page reading.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''
section+='\n'.join(x['path'] for x in inputs)
section+='''
These narrow exceptions authorize NO containing namespace,link,source/primary bundle,earlier exception,role/status/brief/activity alias or other review. No permissions in older files propagate. They are prior-scope/payment/reading-limit context ONLY,not new-family proof reading. Protected bodies AND named metadata stay PRIVATE/local under original rights;copies/excerpts remain only in your private own root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized for this distinct family. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and byte/body access at EVERY depth. Query genuine authored integer/bit arithmetic,tape-layout,convolution,precision/carry,multiplication/division and uniform-algorithm mechanisms as relevant. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivative selection,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through equal/higher headings;record actual extents,truncations/recovery,late reads,coarse omissions and false admissions. If no optional scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162am* *arithmetic*r162am*\n\n'
brief=(prefix+instructions+older+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {'*arithmetic*162am*','*arithmetic*r162am*'}<=rules(brief.decode())
assert brief.split(marker,1)[1]==standing
assert brief.decode().splitlines()[:2]==['Arithmetic discovery r162am — confirmed integer-multiplication operative-proof discovery.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162am/.']
BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,distinct_family=True,source=109,catalogue_extent=[181743,182733],canonical_folders=1,canonical_blobs=18,canonical_entries_including_roots=22,completed_direct_inputs=5,parent_source_body_read=False,new_family_screens=2,source108_skipped_from_historical_user_context=True,R162AL_no_selected_or_frozen_epsilon_free_diagnostic=True,all_older_scopes_preserved=True,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=18,canonical_entries=22,both_new_literal_twins_verified=True,distinct_family=True)))
