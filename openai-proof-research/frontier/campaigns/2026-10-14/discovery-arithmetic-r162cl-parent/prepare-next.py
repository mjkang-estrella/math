#!/usr/bin/env python3
"""Prepare a distinct, fully scoped Source174 discovery task."""
from pathlib import Path
import fnmatch, hashlib, json, re, subprocess
P=Path(__file__).resolve().parents[4];D=Path(__file__).resolve().parent;B=D.parent
N=B/'discovery-arithmetic-r162cm-parent';R=B/'fresh-arithmetic-discovery-r162cm'
BP=B/'expanded-target-2026-10-17/fresh-arithmetic-r162cm-brief.txt'
def sha(a):return hashlib.sha256(a).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,ensure_ascii=False,indent=2)+'\n')
def rules(s):return {z for z in re.findall(r'\*[^\s,;()]*\*',s) if z not in {'*','**'}}
head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=P,text=True).strip()
t=json.loads((B/'tasks.json').read_bytes())
assert t['newAccepted']==19 and t['gpt_subagent_preferences']['serviceTier']=='default'
names=[p.relative_to(P).as_posix() for p in [N,R,BP]];checks=[];legacy=[]
for i,x in enumerate(t['tasks']):
 if i==849 or x.get('status') not in {'running','queued','waiting'}:continue
 if not x.get('brief'):
  assert 'nativeTaskName' in x and 'taskId' not in x;legacy.append(i);continue
 a=(P/x['brief']).read_bytes();assert not x.get('brief_sha256') or sha(a)==x['brief_sha256']
 matches={n:sorted(z for z in rules(a.decode()) if fnmatch.fnmatchcase(n.casefold(),z.casefold())) for n in names}
 assert all(matches.values());checks.append(dict(task_index=i,original_brief=x['brief'],sha256=sha(a),matches=matches))
guard=dict(head=head,before_creation=True,namespaces=names,foreign_initial_brief_checks=checks,legacy=legacy,foreign_live_queries=False)
dump(D/'integration-guard.json',guard)
for p in [N,R,BP]:assert not p.exists(),p
oldbytes=(B/'expanded-target-2026-10-17/fresh-arithmetic-r162cl-brief.txt').read_bytes()
assert sha(oldbytes)=='d6bb28cfcfb7e60c40c84d6ff60831e3eb7f4fd37abe47fd85d43b70bb9f97cb'
old=oldbytes.decode();marker='--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing=old.split(marker,1)[1];assert len(standing.encode())==5570
prefix=old[:old.index('Read COMPLETE Source173')]
prefix=prefix.replace('Arithmetic discovery r162cl — confirmed second-neighborhood operative-proof discovery.','Arithmetic discovery r162cm — confirmed strong-thin-tree operative-proof discovery.',1).replace('fresh-arithmetic-discovery-r162cl/','fresh-arithmetic-discovery-r162cm/',1).replace('FRESH DISTINCT Source173','FRESH DISTINCT Source174',1).replace('Own r162cl I/O','Own r162cm I/O',1)
instructions="""Read BOTH COMPLETE Source174 operative proofs,actual wrappers,ALL includes,figures and references,then strongest relevant primary/companion proofs BEFORE selecting one additional full theorem. The universal C/k cut-thin spanning-tree existence theorem and deterministic polynomial binary-input construction(including binary parallel multiplicities)are ALREADY PAID. Credit all stronger actual hierarchy,sparsification,fixedpoint,signing,fractional-rounding,geometry and extraction operations. Source truth is stipulated;no audit.

Keep one original graph,cut capacities,connectivity parameter and input encoding through the proof. Cut thinness,spectral thinness,cost,degree constraints,packing and algorithmic guarantees are distinct interfaces. Classical/source reductions are paid when compatible. Sustain mathematics;freeze exact full quantifiers only after viable nonroutine feasibility. Parent commissions independent correctness and actual-primary contribution reviews. No self-gates/count,restricted substitute,renamed target or desired-grade retry. Older scopes stay immutable.

R162CL is CLOSED PREFREEZE/no nominee. Lim's actual weighted table plus classical substitution/Hall gives strongly connected36-vertex tournaments with exact matching deficiency1 everywhere,odd-multiple exact deficiencies,and no-strong-vertex examples at all orders>=44. The unrestricted positive Hall direction is FALSE,not a parked gap;scalar Source173 is untouched. This is a paid primary/classical comparison. Fixed-template nonregularity is not a universal regular-tournament obstruction. Full reading/limits and unchanged artifact seal are in parent intake. Parent Source174 operative-proof reading:NONE.
R162CK remains PREFREEZE/no nominee: arbitrary-cardinality original-scale quadratic Ramsey family paid;only specified public-companion conjectural necessities refuted;proved absorption untouched. General secondjet/all-order lifting unproved.
R162CJ remains PREFREEZE/no nominee: positive-surplus prescribed-color cube/reference compatibility paid;zero-surplus extension unproved;balanced example not a counterexample.
R162CI remains PREFREEZE/no nominee: original iid incident-flag constant-factor endpoint unproved;aggregate component paid;repeated-plane/context/retention costs unresolved.
R162CH remains PREFREEZE/no nominee: same-graph/partition/q unimodality unproved;odd quotient/stronger primaries paid;finite examples only reject shortcuts.
R162CG remains PREFREEZE/no nominee: same-ideal weighted aggregate unproved;S6 example satisfies it and defeats stronger shortcuts.
R162CF remains PREFREEZE/no nominee: product-law/tail comparisons paid;energy-weighted sparse bands/variable-radius algebra unresolved.
R162CE remains PREFREEZE/no nominee: local-palette comparisons paid;unrestricted3D pinned coupled estimate/profile transfer unproved,no counterexample.
R162CD remains PREFREEZE/no nominee: one-part-even parity/repair paid;generic tournament/parity bounds unproved,finite singularity not generic failure.
R162CC remains PREFREEZE/no nominee: word planning paid;integer mixed-expression counting/alignment unproved,valuation example limits one template.

R162CB remains CLOSED full-scope PASS/TECHNICAL,condition discharged,ZERO increment. Its immutable theorem:every sufficiently large prime s=2mod3 and every sufficiently large odd n depending on s,r=s^n+1,admits one finite simple r-partite r-uniform hypergraph with exactly r nonisolated vertices per part,cover r,and pairwise intersections1or2. Statement SHA256b69dd8585357682a27bb327cfcd789ebab99c828c00f928ec79322e1b525f53a;proof SHA256c8e2cf054d11162c11b4e2eb0e042820caa493d7d039bee86f670fa33415a25e. No refreeze,repair,renaming or review retry.
R162CA remains PREFREEZE/no nominee:completed same-pattern constructions paid,no new finite-host equality/nonroutine construction. All earlier dispositions remain unchanged.

"""
older=old[old.index('R162BJ remains archived'):old.index('Catalogue access,if needed:')]
historical=old[old.index('R162W is CLOSED'):old.index('Prospective isolation BEFORE')]
isolation=old[old.index('Prospective isolation BEFORE'):old.index(marker)]
sel=json.loads((D/'private/intake/Source174-selection.json').read_bytes());nav=json.loads((D/'private/intake/next-source-navigation.json').read_bytes())
assert sel['catalogue_extent']==[274820,276357] and len(sel['folders'])==2 and len(sel['entries'])==49
blobs=[e for e in sel['entries'] if e['type']=='blob'];texts=[e for e in blobs if not e['path'].endswith('.pdf')]
textbytes=sum(e['size'] for e in texts);assert len(blobs)==38 and len(texts)==36
prior=B/'fresh-arithmetic-discovery-r162cl'
direct=[D/'assessment.md',prior/'private/DERIVATION.md',prior/'private/WORKING.md',prior/'private/READING-LIMITS.md',prior/'FINAL.md'];inputs=[]
for p in direct:
 a=p.read_bytes();inputs.append(dict(path=p.relative_to(P).as_posix(),bytes=len(a),sha256=sha(a),mode=p.stat().st_mode))
section="""Catalogue access,if needed:ONLY binary seek/read sources/CONTENTS.md[274820,276357),EXACT Source174 and BOTH manuscripts. Parent used ONE bounded14000-byte window[274820,288820),decoded only174/175numeric-bold titles and ONLY174body;175body/remainder not decoded;third heading only a byte boundary. ONE new family-body screen. No extra title locator,family screen,whole catalogue read,ancestor inventory or old scan replay.

Confirmed canonical folders and ACTUAL wrappers from complete-tree metadata:
"""
for folder in sel['folders']:
 wrapper=next(e for e in blobs if e['path']==folder+'/build/source/main.tex')
 section+=folder+'\n'+wrapper['path']+';bytes'+str(wrapper['size'])+';Git blob'+wrapper['sha']+'.\n'
section+='Exactly38blobs49entriesincludingroots,36non-PDFtexts'+str(textbytes)+"""bytes,two compiledPDFs. Read BOTH actual build/source/main.tex wrappers and EVERY included mathematical body,all hierarchy subincludes,algorithmic interfaces,figures,macros,bibliographies and READMEs. Authenticate all36text objects in the exact two selected prefixes;do not infer proof completeness from wrappers or headings. Parent operative-source reading:NONE.

Read these FIVE exact COMPLETED originals(project-relative POSIX):
"""+'\n'.join(e['path'] for e in inputs)+"""
These exceptions authorize NO containing namespace,linked source/primary bundle,other review,older exception,role/status/brief/activity alias. No older permission propagates. They supply prior-scope/payment/reading-limit context ONLY. Protected bodies AND metadata remain PRIVATE/local under original rights;copies/excerpts only in your own private root.

At most ONE correctly pruned optional ORIGINAL-history traversal is authorized. Evaluate EVERY inherited literal wildcard/substring on full-project-relative POSIX path.casefold() BEFORE descent,filename eligibility and body access at EVERY depth. Query genuine authored thin-tree,cut-packing,spectral-rounding,signing and graph-hierarchy mechanisms. No projectwide-then-filter scan,ancestor inventory,corpus/role/helper derivatives,size cutoff after eligibility,old scan replay or live peer/task/status/body query. Follow eligible ORIGINAL hits through equal/higher headings;record exact extents,truncations/recoveries,late reads,coarse omissions and false admissions. If no scan is used,say so. No perfect-isolation,exhaustive-history or priority claim.

Seal once with explicit detached anchors and a read-only verifier. Before sealing,sort records,assert uniqueness and preflight SAME final logic. After sealing,change NO sealed file to fit a verifier. Check exact safe membership,hashes,lengths,FULL modes,copies and pinned bindings. Tiny copied controls suffice;do not replace sustained mathematics with administration. Artifact checks are not mathematical gates.

Earlier full scopes/dispositions below are CONTEXT ONLY,not instructions to reopen targets or linked paths:

"""
text=prefix+instructions+older+section+historical+isolation+'\nAdditional prospective literal wildcard twins:\n*arithmetic*162ce* *arithmetic*r162cm*\n'
missing=rules(old)-rules(text)
if missing:text+='\nRemaining inherited literal exclusions:\n'+' '.join(sorted(missing))+'\n'
brief=(text+marker+standing).encode()
assert rules(old)<=rules(brief.decode()) and brief.split(marker.encode(),1)[1]==standing.encode() and len(brief.decode())<120000
assert 'come back to STANDARD speed' in brief.decode() and '*arithmetic*r162cm*' in brief.decode()
N.mkdir(mode=0o700);R.mkdir(mode=0o700);(N/'private').mkdir(mode=0o700)
dump(N/'prospective-isolation.json',guard)
for n,x in [('completed-direct-inputs.json',inputs),('canonical-selection.json',sel),('catalogue-navigation.json',nav)]:
 dump(N/'private'/n,x);(N/'private'/n).chmod(0o600)
BP.write_bytes(brief)
prep=dict(brief=BP.relative_to(P).as_posix(),bytes=len(brief),characters=len(brief.decode()),sha256=sha(brief),standing_bytes_preserved=5570,all_previous_literal_guards_retained=True,all_extra_guard_literals_verified=True,source=174,catalogue_extent=sel['catalogue_extent'],canonical_folders=2,canonical_blobs=38,canonical_entries=49,canonical_text_objects=36,canonical_text_bytes=textbytes,compiled_pdfs=2,new_family_screens=1,body175_not_decoded=True,distinct_family=True,completed_direct_inputs=5,parent_source_body_read=False,serviceTier='default',publication='STOPPED',precreation_oversize_rejections=0,shortening_preserved_all_scopes_and_guards=True)
dump(N/'brief-preparation.json',prep);print(json.dumps(prep))
