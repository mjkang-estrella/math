from pathlib import Path
import json,hashlib,re
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162ct-parent';R=B/'fresh-arithmetic-discovery-r162ct';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162ct-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
for p in [N,R,BP]:assert not p.exists(),p
a=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162cs-brief.txt').read_bytes();assert sha(a)=='0e34dcfeda4839e3750b9ccaf92db88f8076fc506341e0355225def355be6d28'
s=a.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=s.split(marker,1)[1];assert len(standing.encode())==5570
prefix='''Arithmetic r162ct:cycle-decomposition discovery. Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162ct/ (exists empty),including scratch/downloads/copies. EVERY shell workdir /home/mj-kang/Documents/Dev/math/openai-proof-research.
Codex/GPT-6 Astra/high/default;STANDARD speed;19/20 latestR041 overrides obsolete Factory/18. Parent alone grades/counts. No nested agents,git/shared edits,heavy installs,unbounded jobs,publication/uploads/contacts/browser UI or downstream work. Source operative truth at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated;no audit.
Read AGENTS/upstream/full standing brief. Journal ONLY binary[4801,6347),no whole hash/decode. Use complete preprints-tree. Own I/O and FIVE exceptions ONLY override exclusions.
Read COMPLETE Source181/all includes and strongest actual primaries. Full linear cycle/edge partition and stronger constructive/routing/residue operations PAID. Preserve original graph,hypotheses,marks and costs. S176A remains correctness INCOMPLETE/conditional TECHNICAL,condition UNDISCHARGED:zero-error expected-polynomial constructor's Lovasz reconstruction unverified. Do NOT retry,rename or narrow that nominee;seek a distinct nonroutine full-scope operation.
R162CS:PREFREEZE/no nominee. Full arbitrary-edge two-mark Hamiltonian question on cubic3connected bipartite Pfaffian graphs unproved/unfrozen. Fixed-color matching/extraction paid;ONE coloring for ALL marked Hall inequalities missing. Cube/expansion examples reject shortcuts only. Structural167 determinant/extraction paid,2^m evaluations;polynomial filtering unproved,prism refutes unfiltered shortcut only;no retry.
R162CR:PREFREEZE/no nominee. Uniform epsilon n^(1/4) Fourier-modulus deviation for all binaryrows,n>4 unproved/unfrozen. Exact Fourier/first-order reductions paid;common integrality/units/norms missing. Examples reject shortcuts only.

'''
recent=s[s.index('R162CQ remains'):s.index('R162BJ remains archived')];older=s[s.index('R162BJ remains archived'):s.index('Catalogue ONLY')];hist=s[s.index('R162W is CLOSED'):s.index('Prospective isolation BEFORE')];iso=s[s.index('Prospective isolation BEFORE'):s.index(marker)]
sel=json.loads((D/'private/intake/Source181-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[283416,284310]
bs=[e for e in sel['entries'] if e['type']=='blob'];ts=[e for e in bs if not e['path'].endswith('.pdf')];assert len(bs)==11 and len(ts)==10 and sum(e['size'] for e in ts)==111384
prior=B/'fresh-arithmetic-discovery-r162cs';paths=[D/'assessment.md',prior/'private/COMPARISON.md',prior/'WORKLOG.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in paths:
 b=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(b),sha256=sha(b),mode=p.stat().st_mode))
e=next(e for e in ts if e['path'].endswith('/build/main.tex'))
section='''Catalogue ONLY binary[283416,284310),Source181. Parent one14000-byte window[283416,297416):181/182titles and ONLY181body decoded;182body unread,thirdheadingboundaryonly. No extra screen/locator or whole-catalogue read.
ACTUAL wrapper:
'''+e['path']+';bytes'+str(e['size'])+';Git'+e['sha']+'''.
11blobs15entries,10texts111384bytes,onePDF. Read ALL texts/includes/figure/bibliography/README;parent operative reading:NONE.
FIVE exact COMPLETED originals(project-relative POSIX):
'''+ '\n'.join(e['path'] for e in inputs)+'''
ONLY these files,not containers,links,reviews or aliases. Protected bodies AND metadata PRIVATE/local under original rights.
At most ONE optional ORIGINAL-history traversal,COMPLETE guards below before descent/eligibility/body;eligible cycle-decomposition hits through equal/higher headings. Record limits;no exhaustive-clearance/priority claim.
Seal once after SAME-logic preflight:sorted safe membership,hashes,lengths,FULL modes,copies,pins,detached anchors. Then read-only. Tiny controls;no mathematical gates.

'''
text=prefix+recent+older+section+hist+iso+'\nNew literal guards:\n*arithmetic*162ct* *arithmetic*r162ct*\n';missing=rules(s)-rules(text)
if missing:text+='\nOther inherited exclusions:\n'+' '.join(sorted(missing))+'\n'
data=(text+marker+standing).encode();assert rules(s)<=rules(data.decode()) and data.split(marker.encode(),1)[1]==standing.encode();assert len(data.decode())<120000,len(data.decode())
guard=json.loads((D/'intake-prospective-isolation.json').read_bytes());assert guard['before_creation'] and guard['before_semantic_reads'];N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(D/'integration-guard.json',guard);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(data);(N/'capabilities.json').write_bytes((D/'capabilities.json').read_bytes())
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(data),characters=len(data.decode()),sha256=sha(data),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=181,catalogue_extent=sel['catalogue_extent'],canonical_folders=1,canonical_blobs=11,canonical_entries=15,canonical_text_objects=10,canonical_text_bytes=111384,compiled_pdfs=1,new_family_screens=1,body182_not_decoded=True,distinct_canonical_manuscript=True,distinct_from_previous_mathematical_family=True,prior_related_scope_preserved='S176A incomplete correctness; conditional TECHNICAL; no retry',completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED',shortening_preserved_all_scopes_and_guards=True);dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
