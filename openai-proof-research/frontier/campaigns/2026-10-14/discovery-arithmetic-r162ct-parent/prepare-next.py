from pathlib import Path
import json,hashlib,re
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162cu-parent';R=B/'fresh-arithmetic-discovery-r162cu';BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162cu-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
for p in [N,R,BP]:assert not p.exists(),p
a=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162ct-brief.txt').read_bytes();assert sha(a)=='995c4a51396af61270d6b0bab12aad44bde565a63cc32b160362a9c93fe3d02d'
s=a.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n';standing=s.split(marker,1)[1];assert len(standing.encode())==5570
prefix="Arithmetic r162cu:intersective/prime polynomial-difference discovery. Write ONLY frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162cu/ (exists empty). EVERY shell workdir /home/mj-kang/Documents/Dev/math/openai-proof-research.\nCodex/GPT-6 Astra/high/default;STANDARD;19/20 latestR041 overrides obsolete Factory/18. Parent alone grades/counts. No nested agents,git/shared edits,heavy installs,unbounded jobs,publication/uploads/contacts/browser UI or downstream work. Source truth at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated;no audit.\nRead AGENTS/upstream/full standing brief. Journal ONLY binary[4801,6347),no whole hash/decode. Complete preprints-tree. Own I/O and FIVE exact exceptions ONLY override exclusions.\nRead COMPLETE Source182's THREE proofs/includes and operative companions,including prime distribution;credit full source/strongest actual primaries. Preserve hypotheses,original sets,polynomials,uniformity and costs;find a distinct nonroutine full-scope operation.\nR162CT:PREFREEZE/no nominee. All q>=2/all simple graphs:O_q(n) original-edge cycles(0modq)/singletons remains unproved/unfrozen. Local odd-q routing/same-cost representatives paid;global modular splitting/recursion/even-q compatibility missing. Shortcuts only. S176A INCOMPLETE correctness/conditional TECHNICAL unchanged;no retry.\nR162CS:PREFREEZE/no nominee. Arbitrary-edge two-mark Hamiltonian question on cubic3connected bipartite Pfaffian graphs unproved/unfrozen. Fixed-color matching/extraction paid;ONE coloring for ALL marked Hall inequalities missing. Examples reject shortcuts only. Structural167:2^m determinant/extraction paid;polynomial filtering unproved;no retry.\nR162CR:PREFREEZE/no nominee. Uniform epsilon n^(1/4) Fourier-modulus deviation for all binaryrows,n>4 unproved/unfrozen. Exact Fourier/first-order reductions paid;common integrality/units/norms missing. Examples reject shortcuts only.\n\n"
recent=s[s.index('R162CQ remains'):s.index('R162BJ remains archived')];older=s[s.index('R162BJ remains archived'):s.index('Catalogue ONLY')];hist=s[s.index('R162W is CLOSED'):s.index('Prospective isolation BEFORE')];iso=s[s.index('Prospective isolation BEFORE'):s.index(marker)]
sel=json.loads((D/'private/intake/Source182-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes());assert sel['catalogue_extent']==[284310,287105]
bs=[e for e in sel['entries'] if e['type']=='blob'];ts=[e for e in bs if not e['path'].endswith('.pdf')];assert len(bs)==40 and len(ts)==37 and sum(e['size'] for e in ts)==468705
prior=B/'fresh-arithmetic-discovery-r162ct';paths=[D/'assessment.md',prior/'private/COMPARISON.md',prior/'WORKLOG.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in paths:
 b=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(b),sha256=sha(b),mode=p.stat().st_mode))
wrappers=[e for e in ts if e['path'].endswith('/main.tex')];assert len(wrappers)==3
section="""Catalogue ONLY binary[284310,287105),Source182. Parent ONE14000-byte window[284310,298310):182/183titles and ONLY182body decoded;183body unread,thirdheadingboundaryonly. No other catalogue read.
THREE wrappers;read ALL includes:
"""+'\n'.join(e['path'] for e in wrappers)+"""
40blobs54entries,37texts468705bytes,3PDFs. Parent operative reading:NONE.
FIVE exact COMPLETED originals(project-relative POSIX):
"""+'\n'.join(e['path'] for e in inputs)+"""
ONLY these files,not containers,links,reviews or aliases. Protected bodies AND metadata PRIVATE/local under original rights.
At most ONE optional ORIGINAL-history traversal,COMPLETE guards below before descent/eligibility/body;eligible polynomial-difference hits through equal/higher headings. Record limits;no exhaustive-clearance/priority claim.
Seal once after SAME-logic preflight:sorted safe membership,hashes,lengths,FULL modes,copies,pins,detached anchors. Then read-only. Tiny controls;no mathematical gates.

"""
text=prefix+recent+older+section+hist+iso+'\nNew literal guards:\n*arithmetic*162ct* *arithmetic*r162cu*\n';missing=rules(s)-rules(text)
if missing:text+='\nOther inherited exclusions:\n'+' '.join(sorted(missing))+'\n'
text=re.sub(r'\n{2,}', '\n', text)
data=(text+marker+standing).encode();assert rules(s)<=rules(data.decode()) and data.split(marker.encode(),1)[1]==standing.encode();assert len(data.decode())<120000,len(data.decode())
guard=json.loads((D/'intake-prospective-isolation.json').read_bytes());assert guard['before_creation'] and guard['before_semantic_reads'];N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700);dump(D/'integration-guard.json',guard);dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(data);(N/'capabilities.json').write_bytes((D/'capabilities.json').read_bytes())
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(data),characters=len(data.decode()),sha256=sha(data),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=182,catalogue_extent=sel['catalogue_extent'],canonical_folders=3,canonical_blobs=40,canonical_entries=54,canonical_text_objects=37,canonical_text_bytes=468705,compiled_pdfs=3,new_family_screens=1,body183_not_decoded=True,distinct_canonical_manuscript=True,distinct_from_previous_mathematical_family=True,prior_related_scope_preserved='All old frozen/PREFREEZE scopes preserved; no retry',completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED',shortening_preserved_all_scopes_and_guards=True);dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
