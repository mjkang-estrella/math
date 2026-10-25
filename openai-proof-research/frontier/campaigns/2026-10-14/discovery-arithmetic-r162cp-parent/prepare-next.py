"""Close CP without retry and prepare distinct Source178 discovery."""
from pathlib import Path
import hashlib,json,re
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162cq-parent';R=B/'fresh-arithmetic-discovery-r162cq';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162cq-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
t=json.loads((B/'tasks.json').read_bytes());assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
guard=json.loads((D/'contribution-intake-baseline.json').read_bytes());assert guard['before_creation'] and guard['before_semantic_reads']
for p in [N,R,BP]:assert not p.exists(),p
a=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162cp-brief.txt').read_bytes();assert sha(a)=='89fe233241c4639450b704b9529fd4ea07ff6a64cab6720e425d5ee6729e4456'
old=a.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix='''Arithmetic discovery r162cq — confirmed deterministic Ramanujan operative-proof discovery.
Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cq/;root exists empty.
Codex/GPT-6 Astra/high/serviceTier default. Latest user:come back to STANDARD speed. Campaign19/20,latestR041;this overrides obsolete Factory/18 lines below. EVERY command workdir /home/mj-kang/Documents/Dev/math/openai-proof-research. All scratch/downloads/extracts/renders/copies stay in your root. No shared/old/brief edits,git,staging,commits,nested agents,heavy installs,unbounded jobs,publication/uploads/submissions/contacts/browser UI or downstream formal/manuscript/release work. Parent alone assigns reviews/count.
Fresh Source178 conversation;no old-target continuation. All operative source proofs at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are stipulated TRUE;no audit. Read AGENTS.md,upstream.json,complete standing brief and ONLY journal binary[4801,6347). No whole-journal/catalogue decode/hash. Complete preprints-tree.json:13223entries4858136bytes,SHA256eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b;ignore truncated tree.json. Parent checked new paths against recorded foreign INITIAL briefs,not live peers. Own r162cq I/O and FIVE exact exceptions below override broad exclusions only as stated. No perfect-isolation/exhaustive-clearance claim.

'''
instructions='''Read COMPLETE Source178/all includes and strongest actual primary/companion proofs. The full fixed-d/all-large-even-n strict nonbipartite Ramanujan construction and polynomial bit-time output are PAID,as are stronger operative mechanisms. Preserve graph,order,degree,encoding and costs. Source truth stipulated.

R162CP is CLOSED full-scope correctness PASS/contribution TECHNICAL,condition discharged,ZERO increment. Entire unchanged theorem:original Source177 X_m, fixed d>=3 and sufficiently large source odd q,F2 intrinsic weights,all m in a tail; c logV<=S_m<=U_m<=C logV and c logV<=R_m<=C logV. Lower bound covers ALL laws on arbitrary nonlinear sections;linear upper law and affine upper law using one common uniform cut give exact marginals on EVERY primitive fiber. For ALL m>=2, W1(mu_z,mu_z')=Q(z+z'),||z+z'||/3<=Q<=epsilon^-1||z+z'||. Full definitions locked by STATEMENT SHA256ebbecfde0342e866f1401764980ccaf1f3f0c08bc1aea5269e217021774594c9;PROOF7331535f72a9c9dbab2da0396af34c78eb0a1065afb5e96d4cfc618a22a052b6. Actual KN character twisting,source weighted Poincare,tree/orbit averaging and uniform-coset translation pay everything. No refreeze,repair,renaming or desired-grade retry;no runtime lower bound or coefficient/monodromy extension.
Structural175's full n^(-3/5) interior-gap scope stays unproved:bulk inertia,admissibility/diagonal-error compatibility,polynomial finite-support unpaid. No reopening/restriction as new.

'''
recent=old[old.index('R162CO is CLOSED'):old.index('R162BJ remains archived')]
start=recent.index('R162CN is CLOSED');end=recent.index('R162CM is CLOSED')
recent=recent[:start]+'''R162CN remains CLOSED PREFREEZE/no nominee. One fixed complementary two-piece partition for every simple H on at most n vertices with both thresholds O(q(H;n)),same budget1/2,separate embeddings allowed,remains unproved/unfrozen. Generic two-threshold/product-row/adaptive coupling and conditioning/capacity/tensor comparisons are paid;common typicality sufficient but unproved. Cycle defeats regrouping only and admits good paths. Graphic-p_E route not selected. No renamed retry.
'''+recent[end:]
start=recent.index('R162CM is CLOSED');end=recent.index('R162CL is CLOSED')
recent=recent[:start]+'''R162CM remains CLOSED PREFREEZE/no nominee. Exact prescribed marginals on uniformly thin trees of the SAME labelled graph remain unproved/unfrozen. Metric-cone rounding,hull separation,dominated marginals,weighted-Lagrangian lower condition,boundary strongly-Rayleigh laws and label restoration are paid. Joint face/weighted rounding or exact base repair controlling every cut are sufficient unproved routes,not necessities. Triangle rejects peeling only;it has the law. Initial-denominator partitions are stronger. No counterexample/runtime lower bound.
'''+recent[end:]
older=old[old.index('R162BJ remains archived'):old.index('Catalogue:ONLY')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/contribution-intake/Source178-selection.json').read_bytes());nav=json.loads((D/'private/contribution-intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[280658,281794] and len(sel['folders'])==1
blobs=[e for e in sel['entries'] if e['type']=='blob'];texts=[e for e in blobs if not e['path'].endswith('.pdf')];assert len(blobs)==15 and len(texts)==14 and sum(e['size'] for e in texts)==300708
C=B/'arithmetic-r162cp-contribution-r1';A=B/'fresh-arithmetic-discovery-r162cp';direct=[D/'contribution-assessment.md',C/'private/REVIEW.md',C/'private/READING-LIMITS.md',A/'STATEMENT.md',A/'FINAL.md'];inputs=[]
for p in direct:
 b=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(b),sha256=sha(b),mode=p.stat().st_mode))
e=next(e for e in texts if e['path'].endswith('/main.tex'))
section='''Catalogue:ONLY binary sources/CONTENTS.md[280658,281794),EXACT Source178. Parent used ONE14000-byte window[280658,294658),decoded178/179titles and ONLY178body;179body unread,thirdheading boundaryonly. One body screen,no extra locator/screen,whole catalogue,ancestor inventory or oldscan replay.
Confirmed canonical folder and ACTUAL wrapper:
'''+sel['folders'][0]+'\n'+e['path']+';bytes'+str(e['size'])+';Git blob'+e['sha']+'''.
15blobs19entries,14texts300708bytes,onePDF. Read all texts. Parent operative reading:NONE.
Read FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
Exceptions admit ONLY those files,not containers,links,reviews or aliases. No permission propagates;protected bodies AND metadata stay PRIVATE/local under original rights.
At most ONE correctly pruned optional ORIGINAL-history traversal. Apply EVERY inherited wildcard/substring to full-project-relative POSIX path.casefold() BEFORE descent,eligibility/body at every depth. Query authored Ramanujan/interlacing/signing/finite-support mechanisms. No projectwide-then-filter,ancestor inventory,copied corpus,role/helper derivatives,size cutoff,oldscan replay or live peer/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record extents,recovery,late reads,omissions,false admissions. If unused,say so;no exhaustive-clearance/priority claim.
Seal once after SAME-logic preflight:sorted unique safe membership,hashes,lengths,FULL modes,copies,pins,detached anchors. Read-only thereafter;edit NO sealed file. Tiny controls suffice;artifact checks are not mathematical gates.

'''
text=prefix+instructions+recent+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162cq* *arithmetic*r162cq*\n'
missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode();assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode()
assert len(brief.decode())<120000,len(brief.decode())
assert 'come back to STANDARD speed' in brief.decode() and {'*arithmetic*162cq*','*arithmetic*r162cq*'}<=rules(brief.decode())
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(D/'next-integration-guard.json',guard);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=178,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=15,canonical_entries=19,canonical_text_objects=14,canonical_text_bytes=300708,compiled_pdfs=1,new_family_screens=1,body179_not_decoded=True,distinct_canonical_manuscript=True,distinct_from_previous_mathematical_family=True,prior_related_scope_preserved='Structural175',completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED',precreation_oversize_rejections=3,shortening_preserved_all_scopes_and_guards=True)
dump(N/'brief-preparation.json',prep);(N/'capabilities.json').write_bytes((D/'capabilities.json').read_bytes());print(json.dumps(prep))
