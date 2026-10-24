#!/usr/bin/env python3
"""Prepare distinct Source112 work, preserving every old scope and literal guard."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];B=P/'frontier/campaigns/2026-10-14';D=Path(__file__).resolve().parent
N=B/'discovery-arithmetic-r162ao-parent';R=B/'fresh-arithmetic-discovery-r162ao'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162ao-brief.txt'
def sha(raw):return hashlib.sha256(raw).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
def git(*a):return subprocess.check_output(['git',*a],cwd=P)
head=git('rev-parse','HEAD').decode().strip();raw_t=git('show',head+':openai-proof-research/frontier/campaigns/2026-10-14/tasks.json');raw_j=git('show',head+':openai-proof-research/frontier/NEW-TEN-2026-10-14.md')
assert (B/'tasks.json').read_bytes()==raw_t and (P/'frontier/NEW-TEN-2026-10-14.md').read_bytes()==raw_j
assert not git('diff','--cached','--name-only').strip();t=json.loads(raw_t);assert t['newAccepted']==19
names=[x.relative_to(P).as_posix() for x in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
    if i==740 or x.get('status') not in {'running','queued','waiting'}:continue
    if not x.get('brief'):
        assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
    raw=(P/x['brief']).read_bytes();matches={n:[z for z in sorted(rules(raw.decode())) if fnmatch.fnmatchcase(n.casefold(),z.casefold())] for n in names}
    assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(raw),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,original_foreign_brief_guard_checks=checks,legacy_native_without_original_brief=legacy,foreign_live_queries=False,recorded_status_not_live_liveness=True)
dump(D/'integration-guard.json',guard)
assert not N.exists() and not R.exists() and not BP.exists()
N.mkdir();R.mkdir();(N/'private').mkdir();dump(N/'prospective-isolation.json',guard)
original=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162an-brief.txt').read_bytes()
assert sha(original)=='453fba88d197fb21f5aa1c2b40a7a7aab376458ab60871c8e72e0d06e381d7c3'
old=original.decode();marker=b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=original.split(marker,1)[1];assert len(standing)==5570
prefix=old[:old.index('Read the COMPLETE actual Source110')]
prefix=prefix.replace('Arithmetic discovery r162an — confirmed randomized k-server operative-proof discovery.','Arithmetic discovery r162ao — confirmed depth-three Boolean-circuit operative-proof discovery.',1)
prefix=prefix.replace('Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162an/.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ao/.',1)
prefix=prefix.replace('FRESH DISTINCT Source110','FRESH DISTINCT Source112',1).replace('Own r162an I/O','Own r162ao I/O',1)
instructions='''Read the COMPLETE actual Source112 theorem/proof construction and strongest operative primary/companion interfaces BEFORE selecting a full result. The ENTIRE stipulated explicit depth-three lower bound is ALREADY PAID:ONE language in deterministic polynomial time whose n-bit membership function requires 2^(omega(sqrt(n))) TOTAL gates in unbounded-fan-in OR-AND-OR circuits at EVERY sufficiently large input length,including the bottom layer. Read the actual stronger quantitative constructions and exact gate/input/negation conventions instead of treating this headline as the entire paid interface. Do not audit upstream truth,nominate this theorem itself,or count routine padding,duality,basis translation,composition or familiar consequences already supplied by the strongest compatible source/primary proof.

Track ONE language and its uniform membership algorithm,all-length versus infinitely-often quantifiers,polynomial time/description/constructibility,asymptotic versus effective parameters,gate/wire/bottom-layer counts,depth and fan-in,literals/negations,deterministic/randomized/nondeterministic models,exact/approximate functions and distributions,promises,restrictions,advice,preprocessing and every parameter/encoding cost. A method-limit,failed naive transfer or unproved uniformity bridge is not a substantial finding. Read actual primary mechanisms before selecting ONE promising full operation and do sustained mathematics. Freeze every hypothesis,quantifier,constant and conclusion only when a viable full theorem emerges,before extended proof drafting. Parent alone commissions independent correctness and substantial-contribution gates. No restricted/renamed substitute or desired-grade retry for an older full target.

R162AN is archived PREFREEZE/no nominee. Preserve its FULL unproved diagnostic:ONE finite-alphabet finite-bit randomized program and ONE numerical integer C>=1,EVERY explicit n-point positive-rational metric n>=3,2<=k<n,and EVERY labeled initial k-tuple including collisions. Complete input length L includes all distance numerators/denominators,n,k,s,field lengths and delimiters. Preprocessing<=C(L+2)^C;EVERY reachable request-t history has bit cost<=C(L+ceil(log2(t+1))+2)^C,including arithmetic,movement,input,randomness and output. Requests move at most one labeled server;hits may have zero movement. Across the ENTIRE execution including preprocessing,at most C ceil(log2(k+1)) independent unbiased bits TOTAL are read. ONE policy per instance/start must serve ALL finite OBLIVIOUS request words with expected cost<=C log2(k+1)^2 OPT+B(X,k,s),B finite nonnegative and independent of word/horizon,with NO polynomial bound required. No adaptive adversary,tail/pathwise ratio,zero-additive,infinite-metric,metric-oracle or deterministic strengthening is included. Neither this diagnostic nor its negation is proved;no theorem was frozen,gate assigned or count changed.

The strongest integrated paid reduction already supplies ceil(log2 binom(n,k)^2)<=2k log2(en/k)+1 random bits TOTAL with the same ratio and uniform bit/additive conventions. It pays rational shared-prefix laws,configuration transport quantization,integral agent matching,lazy service,deterministic input-only filters,pathwise first-use correction,one seed reused across epochs,and terminating delayed construction. Finite randomness alone is paid. Unpaid:ONE poly(k)-sized causal ensemble with joint all-word cost control,or another complete algorithm. Local k-way matching does not pay empirical granularity;configurationwise domination and law-by-law minimax have specific capacity/support limits. Proximal examples,moving-pedestal transport accounting,finite-horizon sampling and an elementary seed scale check are specific comparisons,not lower bounds or necessary/exhaustive routes. Favorable n regimes,fixed HSTs and repeated-seed reductions do not replace the full target. Both canonical texts were completely read;transitive primary ancestry incomplete,no optional original-history traversal;one read-only own-notes command-workdir deviation is disclosed. Do not reopen that diagnostic or a weaker substitute in this circuit family.

'''
older=old[old.index('R162AM is archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
nav=json.loads((D/'private/intake/next-source-navigation.json').read_text());selected=json.loads((D/'private/intake/Source112-selection.json').read_text())
assert len(selected['folders'])==1 and len(selected['entries'])==19
blobs=[x for x in selected['entries'] if x['type']=='blob'];assert len(blobs)==13
folder=selected['folders'][0];wrapper=next(x for x in blobs if x['path']==folder+'/build/latex/main.tex')
assert wrapper['size']==1072 and wrapper['sha']=='77d2183a9bea307a8980a2aa6daf48b39ffffd14'
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162an/private/MATH.md',B/'fresh-arithmetic-discovery-r162an/private/SOURCE-COMPARISON.md',B/'fresh-arithmetic-discovery-r162an/private/READING-LIMITS.md',B/'fresh-arithmetic-discovery-r162an/private/FINAL.md']
inputs=[]
for f in direct:
    raw=f.read_bytes();inputs.append(dict(path=f.relative_to(P).as_posix(),bytes=len(raw),sha256=sha(raw),mode=f.stat().st_mode))
dump(N/'private/completed-direct-inputs.json',inputs);dump(N/'private/canonical-selection.json',selected);dump(N/'private/catalogue-navigation.json',nav)
section=f'''Catalogue access,if needed: ONLY binary seek/read sources/CONTENTS.md[186010,186982),EXACT Source112. Parent used ONE bounded14000-byte window at184788,decoded only FIRST TWO numeric-bold TITLE STRINGS111/112,then selected ONLY112 body. Source111 TITLE was skipped because historical USER handoff already identifies Structural151 Source111 prophet research with an unpaid target;NO Source111 catalogue body or protected historical body was read. Heading113 supplied ONLY a byte boundary,no title/body decode. ONE new family body screened. No child title locator,extra family/catalogue screen,whole catalogue read,ancestor hunt or old scan replay. This is bounded navigation,not exhaustive clearance.

Confirmed canonical folder:
{folder}
ACTUAL wrapper from complete-tree metadata:
{wrapper['path']}
bytes1072;Git blob77d2183a9bea307a8980a2aa6daf48b39ffffd14.
There are13 blobs/19 entries including root. Parent source-proof reading:NONE. Fetch exact pinned raw paths and follow actual textual includes;do not guess root main.tex,build/main.tex or build/source/. Authenticate selected objects,read complete operative proofs,and distinguish PDF/metadata authentication from semantic or rendered-page reading.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''
section+='\n'.join(x['path'] for x in inputs)
section+='''
These narrow exceptions authorize NO containing namespace,linked source/primary bundle,older direct exception,role/status/brief/activity alias or other review. No permissions in older files propagate. They are prior-scope/payment/reading-limit context ONLY,not this family's operative source reading. Protected bodies AND their named metadata remain PRIVATE/local under original rights;copies/excerpts stay only in your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized for this distinct family. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and byte/body access at EVERY depth. Query genuine authored Boolean-circuit lower-bound,restrictions,depth,explicit-language,communication and composition mechanisms as relevant. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL operative hits through equal/higher headings;record exact extents,truncation/recovery,late reads,coarse omissions and false admissions. If no optional scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
extra='\nAdditional prospective literal wildcard twins for this distinct round:\n*arithmetic*162ao* *arithmetic*r162ao*\n\n'
brief=(prefix+instructions+older+section+historical+isolation+extra+marker.decode()).encode()+standing
assert rules(old)<=rules(brief.decode()) and {'*arithmetic*162ao*','*arithmetic*r162ao*'}<=rules(brief.decode())
assert brief.split(marker,1)[1]==standing
assert brief.decode().splitlines()[:2]==['Arithmetic discovery r162ao — confirmed depth-three Boolean-circuit operative-proof discovery.','Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ao/.']
BP.write_bytes(brief)
dump(N/'brief-preparation.json',dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,distinct_family=True,source=112,catalogue_extent=[186010,186982],canonical_folders=1,canonical_blobs=13,canonical_entries_including_roots=19,completed_direct_inputs=5,parent_source_body_read=False,new_family_screens=1,source111_body_not_decoded=True,heading113_byte_boundary_only=True,full_k_server_total_randomness_diagnostic_preserved=True,all_older_scopes_preserved=True,publication='STOPPED'))
print(json.dumps(dict(brief_bytes=len(brief),brief_sha256=sha(brief),foreign_original_briefs_checked=len(checks),canonical_blobs=13,canonical_entries=19,both_new_literal_twins_verified=True,distinct_family=True)))
