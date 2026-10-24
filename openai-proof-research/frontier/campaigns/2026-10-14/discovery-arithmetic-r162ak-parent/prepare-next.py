#!/usr/bin/env python3
"""Prepare fresh Source107 work, preserving every older scope and literal guard."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4]
B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162al-parent';R=B/'fresh-arithmetic-discovery-r162al'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162al-brief.txt'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
raw_t=subprocess.check_output(['git','show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json'],cwd=P)
raw_j=subprocess.check_output(['git','show',head+':openai-proof-research/frontier/NEW-TEN-2026-10-14.md'],cwd=P)
assert (B/'tasks.json').read_bytes()==raw_t and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()==raw_j
assert not subprocess.check_output(['git','diff','--cached','--name-only'],cwd=P).strip()
t=json.loads(raw_t);assert t['newAccepted']==19
names=[x.relative_to(P).as_posix() for x in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
    if i==735 or x.get('status') not in {'running','queued','waiting'}:continue
    if not x.get('brief'):
        assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
    raw=(P/x['brief']).read_bytes();matches={n:[z for z in sorted(rules(raw.decode())) if fnmatch.fnmatchcase(n.casefold(),z.casefold())] for n in names}
    assert all(matches.values()),(i,matches)
    checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(raw),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,foreign_live_queries=False,recorded_status_not_live_liveness=True)
dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists()
N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162ak-brief.txt').read_bytes()
assert sha(original)=='68e33ce8dbf4c7410624c3633a08296f205d9c38595cea75897911faf41013fb'
old=original.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=original.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read the COMPLETE actual Source105')]
prefix=prefix.replace('Arithmetic discovery r162ak — confirmed perfect-completeness 2-to-1 operative-proof discovery.','Arithmetic discovery r162al — confirmed matrix-multiplication operative-proof discovery.',1)
prefix=prefix.replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ak/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162al/.',1)
prefix=prefix.replace('FRESH DISTINCT Source105','FRESH DISTINCT Source107',1).replace('Own r162ak I/O','Own r162al I/O',1)
instructions='''Read the COMPLETE actual Source107 theorem/proof constructions and strongest operative companions/primary interfaces BEFORE selecting a full result. All stipulated square and rectangular bounds and their stronger proof operations are ALREADY PAID:omega<=9/4 over C with O_epsilon(n^(9/4+epsilon)) arithmetic operations;the stated characteristic-zero dual/rectangular results(alpha>0.465 and omega(1,0.709,1)<2.092);the companion square<2.258 bound with its actual characteristic exceptions;and the every-fixed-field square<2.371054886006746 construction. Read exact hypotheses,strictness,constants and operative proofs instead of assuming the catalogue states all interfaces. Do not audit their truth,rerun upstream certificates as a new proof,or nominate routine exponent substitutions and familiar applications already supplied by the strongest compatible composition.

Track field/characteristic dependence,finite exceptional primes,uniform versus fixed-field/fixed-epsilon constants,arithmetic-operation versus binary-bit cost,rectangular aspect ratios,exact versus border algorithms,interpolation and denominator costs,coefficient heights,extension fields,uniform construction/description and finite input/output costs. A standard exactification or application can be paid even when one naive composition fails. Do not infer substantial contribution from a failed transfer or an unproved uniformity bridge. Choose ONE promising full operation only after actual source and primary proof reading;perform sustained mathematical work and close the full statement. When a viable theorem emerges,freeze every quantifier,hypothesis,constant and conclusion before extended proof drafting. Parent alone commissions independent correctness and contribution gates. Do not create restricted/renamed replacements or retries for desired grades.

R162AK is archived PREFREEZE/no nominee. Its full R remains unproved,neither R nor its negation established. For EVERY fixed rational delta in(0,1),R asks for a deterministic polynomial-BIT-time reduction from EVERY explicit3-CNF formula to a nonempty explicit unweighted exact-two projection multigraph with alphabets[2q],[q],q=q(delta)>=2,no isolated retained questions,and at EACH individual left vertex EXACTLY the uniform distribution on ALL(2q-1)!! perfect matchings across incident edge OCCURRENCES. YES has ONE labeling satisfying EVERY occurrence;NO has value<=delta. All tables,IDs,multiplicities,delimiters and output/runtime costs are charged;constants may depend on delta,no varying-delta uniformity or degree restriction. Averaged richness,partial matching families,near-perfect completeness or a different soundness promise do not replace R.

Paid R comparisons include the full ordinary exact-two source construction,its stronger independent-set companion,actual Unique-to-rich conversion and covering/low-rank interfaces. Retained author calculations give exact matching-mass capacity and private-filler value floors,an exact completeness loss for a specified compatible composite,coordinate-factorization probabilities with one common coarsening labeling,and simultaneous-coordinate square constraints. These are specific-construction limits,not impossibility for R. Unpaid:ONE construction and own-question decoder on the SAME full uniform-matching edge distribution retaining ONE exact-completeness labeling and the entire fixed-delta bit budget. Do not reopen R or a weaker substitute in this matrix family. Canonical/explicit companion reading was complete;transitive primary ancestry incomplete,no optional original-history traversal. These older inputs are scope/payment context,not your new-family reading.

'''
game=old[old.index('R162AJ is a FULL'):old.index('This distinct family does NOT retry')]
first_end=game.index('Its exact frozen scope')
game=('R162AJ is CLOSED PASS/TECHNICAL. Independent correctness PASS for the ENTIRE unchanged frozen theorem AND proof has been adopted,relative to stipulated upstream truth;the full-scope TECHNICAL contribution condition is DISCHARGED. No acceptance or count. No grade retry,renamed/restricted replacement or downstream work. Only the exact parent closure assessment below is newly admitted;no review namespace or linked body permission propagates.\n\n'+game[first_end:])
game=game.replace('Do not develop this game nominee in the new2-to-1 family.','Do not develop this closed game nominee in the matrix-multiplication family.')
old_scopes=old[old.index('This distinct family does NOT retry'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
nav=json.loads((D/'private/intake/next-source-navigation.json').read_text())
selected=json.loads((D/'private/intake/Source107-selection.json').read_text())
assert len(selected['folders'])==3 and len(selected['entries'])==104
blobs=[x for x in selected['entries'] if x['type']=='blob'];assert len(blobs)==82
paths=[selected['folders'][0]+'/build/paper.tex',selected['folders'][1]+'/build/main.tex',selected['folders'][2]+'/build/main.tex']
wrappers=[next(x for x in blobs if x['path']==n) for n in paths]
assert [x['size'] for x in wrappers]==[43060,3238,1977]
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162ak/private/PREFREEZE-SCOPE.md',B/'fresh-arithmetic-discovery-r162ak/private/MATH.md',B/'fresh-arithmetic-discovery-r162ak/private/READING-LIMITS.md',B/'discovery-arithmetic-r162aj-parent/proof-assessment.md']
inputs=[]
for f in direct:
    raw=f.read_bytes();inputs.append(dict(path=f.relative_to(P).as_posix(),bytes=len(raw),sha256=sha(raw),mode=f.stat().st_mode))
dump(N/'private/completed-direct-inputs.json',inputs);dump(N/'private/canonical-selection.json',selected);dump(N/'private/catalogue-navigation.json',nav)
section='''Catalogue access,if needed: ONLY binary seek/read sources/CONTENTS.md[178483,180526),EXACT Source107. Parent used ONE bounded14000-byte window at177336,decoded only numeric-bold TITLE STRINGS106/107 and selected107 body;next heading was only a byte boundary. Source106 is the directly cited independent-set companion already read in r162ak,so it is not the fresh family. Disclosure:an initial incorrect heading-regex diagnostic printed first170 window bytes,incidentally exposing a partial106 description;the SAME window was reread for recovery. No further family/catalogue screen is authorized. No whole catalogue opening/decoding,ancestor hunt or child title locator. This is bounded navigation,not a clean/exhaustive isolation certificate.

Confirmed Source107 canonical folders and ACTUAL wrappers from complete-tree metadata follow. There are82 blobs/104 entries including folder roots. Parent operative-proof reading:NONE. Authenticate selected objects and follow actual textual includes;do not guess root main.tex or confuse build/paper.tex with a nonexistent main.tex. Metadata and hashes are not semantic proof reading. All three actual source/companion constructions and their stronger operative deductions are stipulated TRUE.
'''
for f,w in zip(selected['folders'],wrappers):section+=f'\n{f}\nACTUAL WRAPPER {w["path"]}\nbytes{w["size"]};Git blob{w["sha"]}.\n'
section+='\nRead these FIVE exact COMPLETED originals(project-relative POSIX):\n'+'\n'.join(x['path'] for x in inputs)
section+='''
These narrow exceptions authorize no containing namespace,link,source/primary bundle,earlier direct exception,role/status/brief/activity alias or other review. No permission in those older files propagates. They are scope/payment and reading-limit context only,not new-family operative source reading. Protected bodies AND named metadata remain private/local under original rights;copies/excerpts stay only in your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized for this new family. Evaluate EVERY inherited literal wildcard/substring on the full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and byte/body access at every depth. Query genuine authored mechanisms for matrix multiplication,tensor extraction,border/exact rank,rectangular algorithms,arithmetic complexity and field/bit uniformity as relevant. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through equal/higher headings,record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If no optional scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162al* *arithmetic*r162al*\n\n'
brief=(prefix+instructions+game+old_scopes+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode())
assert {'*arithmetic*162al*','*arithmetic*r162al*'}<=rules(brief.decode())
assert brief.split(marker,1)[1]==standing
assert brief.decode().splitlines()[:2]==['Arithmetic discovery r162al — confirmed matrix-multiplication operative-proof discovery.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162al/.']
BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,distinct_family=True,source=107,catalogue_extent=[178483,180526],canonical_folders=3,canonical_blobs=82,canonical_entries_including_roots=104,completed_direct_inputs=5,parent_source_body_read=False,source106_is_already_paid_companion=True,navigation_prefix_overread_disclosed=True,R162AJ_PASS_TECHNICAL_condition_discharged=True,R162AK_full_R_preserved=True,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=82,canonical_entries=104,both_new_literal_twins_verified=True,distinct_family=True)))
