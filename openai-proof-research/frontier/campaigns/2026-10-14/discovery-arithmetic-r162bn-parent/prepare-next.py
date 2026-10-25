#!/usr/bin/env python3
"""Prepare a distinct full-scope Source148 discovery at standard speed."""
from pathlib import Path
import fnmatch,hashlib,json,re,subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162bo-parent';R=B/'fresh-arithmetic-discovery-r162bo';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162bo-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip();t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==821 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names};assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False);dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162bn-brief.txt').read_bytes();assert sha(oldbytes)=='1e383dbdf52e5b9844cd9491580b86ecc46671aed4ea25b83943adb104d67284'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read BOTH complete actual Source147')].replace('Arithmetic discovery r162bn — confirmed near-boundary billiard-rigidity operative-proof discovery.','Arithmetic discovery r162bo — confirmed entropy-rate dimension operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162bn/','fresh-arithmetic-discovery-r162bo/',1).replace('FRESH DISTINCT Source147','FRESH DISTINCT Source148',1).replace('Own r162bn I/O','Own r162bo I/O',1)
instructions='''Read the COMPLETE actual Source148 operative proof,actual build/main.tex,ALL mathematical sections,references and strongest relevant primary/companion interfaces BEFORE selecting ONE additional full theorem. The ENTIRE stipulated result is ALREADY PAID:every finite real self-similar measure on the line has dim_H(mu)=min(1,h_RW/chi),with random-composed-MAP entropy rate and average logarithmic contraction,allowing exact overlaps and unequal/negative contraction ratios,without a separation assumption. Read every stronger actual entropy,concentration,window,pair,type,limit and quantitative operation;the catalogue headline is not the proof's scope boundary. Do not audit source truth or nominate the supplied formula.

Keep the SAME probability measure,actual composed affine maps,overlap equivalence,contraction cocycle and entropy convention throughout a proposed construction. Symbolic entropy need not equal entropy of distinct composed maps. Exact overlap,near overlap,orientation reversal and variable contraction scales must retain their actual hypotheses. Uniformity across measures/parameters,finite-scale errors,conditional/Markov laws,higher dimension or different spectra require their additional interfaces;standard blocking,coding,ergodic/information and dimension-transfer operations are paid where strongest ACTUAL assumptions hold. Read primary operative proofs before declaring compatibility a new obstacle. Do not rename or reopen the existing Salem,nonstationary,Markov,entropy-overlap or other full targets described below.

Perform sustained mathematical derivation after complete source and strongest relevant primary reading. Choose ONE genuinely additional operation;freeze every hypothesis,quantifier,constant,measure and limit convention only when a complete nonroutine proof is viable,then prove the ENTIRE scope. Parent alone commissions independent correctness and separate actual-primary substantial-contribution reviews. No self-gates/count,desired-grade retry,narrowing or scope renaming. No exhaustive-history,never-investigated or worldwide-priority claim.

R162BN is archived PREFREEZE/no nominee. Both complete Source147 billiard proofs and all stronger analytic/joint/continuation/cone/critical-model/sign-test operations are PAID. An available exact rational periodic graph already supplies its first parameter jet. A full area-ordered foliation preserved setwise with its grazing end is individually preserved by the finite-area leaf label;this is also a paid elementary reduction. The retained Euclidean chord action calculation gives one common second-order radial correction for the entire1/q tail,including all multiple harmonics. A cubic shared-harmonic calculation at denominators6/12 rules out ONE specified fourth-mode continuation;an abstract sparse-root analytic example limits one division inference. Neither is a general billiard impossibility or an exact caustic construction.

Missing rational leaves and their common analytic compatibility on the SAME positively curved Euclidean table remain unproved;no theorem/diagnostic frozen. Both complete source proofs28texts601146bytes read,30blobs39entries authenticated;2PDFsauthonly. Primary154pages across6PDFs count different versions separately,2fullpapers plus complete published dynamical proof,3already-counted pages rendered. Exact version,late-read,recovery and ancestry limits disclosed;history0. Parent/bundled artifact MATCH75payloads10346795bytes77files17dirs;5original/copy pairs and allseals unchanged. These are artifact checks,not mathematical grades.

R162BM remains CLOSED correctnessPASS/contributionTECHNICAL at its full unchanged standard-map entropy asymptotic. Original arrays,elementary moments,small initial second moments,and matching initial/terminal positive cap subtraction already pay additive o(1). No re-review,relabeling or contribution-count retry. All older scopes/dispositions remain unchanged;one substantial acceptance still needed.

'''
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')];isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source148-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes())
assert sel['catalogue_extent']==[243744,244844] and len(sel['folders'])==1 and len(sel['entries'])==13
blobs=[e for e in sel['entries'] if e['type']=='blob'];assert len(blobs)==10 and sum(e['size'] for e in blobs if not e['path'].endswith('.pdf'))==77648
wrapper=next(e for e in blobs if e['path']==sel['folders'][0]+'/build/main.tex');assert wrapper['size']==2261 and wrapper['sha']=='e545389b85c7d09dcc5381e460c707b9a74fd8bc'
direct=[D/'assessment.md',B/'fresh-arithmetic-discovery-r162bn/private/DERIVATION.md',B/'fresh-arithmetic-discovery-r162bn/private/WORKING.md',B/'fresh-arithmetic-discovery-r162bn/private/SOURCE-INTERFACES.md',B/'fresh-arithmetic-discovery-r162bn/private/READING-LIMITS.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section='''Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[243744,244844),EXACT Source148. Parent used one bounded14000-byte window[243744,257744),decoding only148/149numeric-bold titles and ONLY148body;149body/remainder not decoded;third heading ONLY byte boundary. The SAME window was reread once to recover a metadata selector's paper.pdf assumption;the actual linked file is main.pdf. No additional family/body screen occurred. No child title locator,extra family screen,whole catalogue read,ancestor inventory or old scan replay. Navigation is not exhaustive clearance.

Confirmed canonical folder and ACTUAL wrapper from complete-tree metadata:
'''+sel['folders'][0]+'\n'+wrapper['path']+';bytes2261;Git blob'+wrapper['sha']+'''.
Combined10blobs13entriesincludingroot,9textualobjects77648bytes and one compiled main.pdf. Read ALL operative texts including all six sections,actual wrapper,README and references. Authenticate exact bytes;metadata/abstracts are not proof reading. Parent operative-source reading:NONE. lean/docs/148.md,if present,is scoped comparator navigation only;no downstream formalization.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
These narrow exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND named metadata remain PRIVATE/local under original rights;copies/excerpts only inside your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored self-similar-measure,entropy-rate,overlap,coding,conditional-scale and dimension mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check safe exact membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

'''
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162bo* *arithmetic*r162bo*\n'
missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162bo*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=148,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=10,canonical_entries=13,canonical_text_objects=9,canonical_text_bytes=77648,compiled_pdfs=1,new_family_screens=1,body149_not_decoded=True,catalogue_link_selector_recovery_disclosed=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED')
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
