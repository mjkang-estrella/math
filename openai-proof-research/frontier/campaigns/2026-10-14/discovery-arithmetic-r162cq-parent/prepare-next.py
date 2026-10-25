from pathlib import Path
import json,hashlib,re
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162cr-parent';R=B/'fresh-arithmetic-discovery-r162cr';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162cr-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
for p in [N,R,BP]:assert not p.exists(),p
old=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162cq-brief.txt').read_bytes();assert sha(old)=='bb329e024431f33198e42ea00a2114931d110327991113768bb76ee63d4fd2b5'
s=old.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=s.split(marker,1)[1];assert len(standing.encode())==5570
prefix=s[:s.index('Read COMPLETE Source178')].replace('r162cq','r162cr').replace('deterministic Ramanujan','circulant Hadamard and Barker').replace('Source178','Source179')
prefix=prefix.replace('Fresh Source179 conversation;no old-target continuation. ','').replace('Parent checked new paths against recorded foreign INITIAL briefs,not live peers. Own r162cr I/O and FIVE exact exceptions below override broad exclusions only as stated. No perfect-isolation/exhaustive-clearance claim.','Parent prechecked paths;own r162cr I/O and FIVE exact exceptions ONLY override guards. No live queries or exhaustive-clearance claim.')
intro='''Read COMPLETE Source179/includes and actual strongest primary/companion proofs. Both full classifications and stronger operations are PAID. Preserve alphabets,periodic/aperiodic conventions,parameters/quantifiers;source truth stipulated.
R162CQ remains PREFREEZE/no nominee. Same-law logarithmic-girth preservation through the full source repair and finite seed space is paid. Prescribed-base signing and finite-cover attempts remain unclosed/unfrozen. Fourth-moment joint control is missing;the triangle response loses surplus at the3-cycle channel. These are shortcut failures,not full counterexamples. Stronger primary signing,covering and mixed-moment operations are paid. No old target is reopened.

'''
recent=s[s.index('R162CP is CLOSED'):s.index('R162BJ remains archived')]
start=recent.index('R162CP is CLOSED');end=recent.index('Structural175')
recent=recent[:start]+'''R162CP CLOSED full-scope PASS/TECHNICAL,condition discharged,ZERO increment. Original Source177 X_m,fixed d>=3/sufficient source odd q,F2 intrinsic weights,all m in a tail:c logV<=S<=U<=C logV,c logV<=R<=C logV. Lower:ALL nonlinear-section laws. Upper:linear sections,one common uniform-cut affine shift with exact marginals on EVERY fiber. ALL m>=2:W1(mu_z,mu_z')=Q(z+z'),||z+z'||/3<=Q<=epsilon^-1||z+z'||. Definitions locked by STATEMENT ebbecfde0342e866f1401764980ccaf1f3f0c08bc1aea5269e217021774594c9;PROOF7331535f72a9c9dbab2da0396af34c78eb0a1065afb5e96d4cfc618a22a052b6. KN character twisting,source weighted Poincare,tree/orbit averaging and coset translation pay all. No refreeze/repair/renamed retry;no runtime lower bound or coefficient/monodromy extension.
'''+recent[end:]
older=s[s.index('R162BJ remains archived'):s.index('Catalogue:ONLY')];hist=s[s.index('R162W is CLOSED'):s.index('Prospective isolation BEFORE')];iso=s[s.index('Prospective isolation BEFORE'):s.index(marker)]
sel=json.loads((D/'private/intake/Source179-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[281794,282674]
bs=[e for e in sel['entries'] if e['type']=='blob'];ts=[e for e in bs if not e['path'].endswith('.pdf')];assert len(bs)==10 and len(ts)==9 and sum(e['size'] for e in ts)==50986
prior=B/'fresh-arithmetic-discovery-r162cq';paths=[D/'assessment.md',prior/'private/COMPARISON.md',prior/'WORKLOG.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in paths:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
e=next(e for e in ts if e['path'].endswith('/main.tex'))
section='''Catalogue:ONLY binary sources/CONTENTS.md[281794,282674),Source179. Parent used ONE14000-byte window[281794,295794),only179body and179/180titles decoded;180body unread,thirdheading boundaryonly. One screen,no extra locator/screen,whole catalogue,ancestor inventory or oldscan replay.
Canonical folder/wrapper:
'''+sel['folders'][0]+'\n'+e['path']+';bytes'+str(e['size'])+';Git'+e['sha']+'''.
10blobs13entries,9texts50986bytes,onePDF. Read all text/includes. Parent operative reading:NONE.
FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
Exceptions admit ONLY those files,not containers,links/reviews/aliases. No permission propagates. Protected bodies AND metadata stay PRIVATE/local under original rights.
At most ONE pruned optional ORIGINAL-history traversal. Apply EVERY inherited full-project-relative POSIX casefold wildcard/substring BEFORE descent,eligibility/body at EVERY depth. Query authored circulant-Hadamard/Barker/autocorrelation/cyclotomic mechanisms. No projectwide-then-filter,ancestor inventory,copied corpus,role/helper derivatives,size cutoff,oldscan replay or live peer/status/body query. Follow eligible originals to equal/higher headings;record actual extents,recovery,late reads,omissions,false admissions. If unused,say so;no exhaustive-clearance/priority claim.
Seal once after SAME-logic preflight:sorted safe unique membership,hashes,lengths,FULL modes,copies,pins,detached anchors. Read-only thereafter;no sealed edits. Tiny controls suffice;artifact checks are not mathematical gates.

'''
text=prefix+intro+recent+older+section+hist+iso+'\nNew literal guards:\n*arithmetic*162cr* *arithmetic*r162cr*\n';missing=rules(s)-rules(text)
if missing:text+='\nOther inherited exclusions:\n'+' '.join(sorted(missing))+'\n'
data=(text+marker+standing).encode();assert rules(s)<=rules(data.decode()) and data.split(marker.encode(),1)[1]==standing.encode();assert len(data.decode())<120000,len(data.decode())
guard=json.loads((D/'intake-prospective-isolation.json').read_bytes());assert guard['before_creation'] and guard['before_semantic_reads'];N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(D/'integration-guard.json',guard);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(data);(N/'capabilities.json').write_bytes((D/'capabilities.json').read_bytes())
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(data),characters=len(data.decode()),sha256=sha(data),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=179,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=10,canonical_entries=13,canonical_text_objects=9,canonical_text_bytes=50986,compiled_pdfs=1,new_family_screens=1,body180_not_decoded=True,distinct_canonical_manuscript=True,distinct_from_previous_mathematical_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED',precreation_oversize_rejections=2,shortening_preserved_all_scopes_and_guards=True);dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
