#!/usr/bin/env python3
"""Prepare one isolated planar-energy discovery brief without dispatching."""
from pathlib import Path
import hashlib
import json
import re

P = Path(__file__).resolve().parents[4]
B = P / 'frontier/campaigns/2026-10-14'
D = Path(__file__).resolve().parent
old_raw = (B / 'expanded-target-2026-10-17/fresh-arithmetic-r162y-brief.txt').read_bytes()
marker = b'--- COMPLETE ORIGINAL STANDING BRIEF (two obsolete lines overridden above) ---\n'
standing = old_raw.split(marker, 1)[1]
assert len(standing) == 5570
old = old_raw.decode()
prefix = old[:old.index('Catalogue access, if needed:')]
prefix = prefix.replace('r162y', 'r162z').replace('Source089', 'Source090').replace('graph-metric operative-proof discovery', 'planar-energy operative-proof discovery').replace('TWO confirmed companions', 'FOUR confirmed companions')
isolation = old[old.index('Prospective isolation BEFORE'):old.index(marker.decode())]
previous = '''Arithmetic162y is CLOSED PREFREEZE/no nominee, with no frozen theorem or gate. Its FULL diagnostic asks ONE numerical C with real L1 distortion <=C log(k+1) for EVERY k>=2,EVERY finite connected undirected graph admitting bags of size <=k,and EVERY positive real edge-length assignment;ONE embedding for ALL vertex pairs,independent of n,aspect ratio,degree,decomposition depth,lengths and terminal choices. No planarity or algorithmic/bit-runtime claim. Source n-independent C_k,primary min-comparison O(sqrt(log(k+1)log n)),optimal-padding co-bag launch c/log(k+1),reservoir dissipation,full-assignment-versus-pair-metric distinction,one-scale cuts,measured descent,conditional planar persistence,exact finite cut-cone LP and tree check are PAID. Remaining is ONE joint all-scale/all-branch cut/capacity-demand estimate with O(log(k+1)) loss against the SAME original capacity budget. Through the exact finite LP this residual is equivalent to the diagnostic; source-specific reservoir/persistence constructions are sufficient routes only. Local improved padding does not remove the common upper budget,full separator-assignment marginal or anchor transport costs. No per-pair/per-scale winning witnesses,restricted lengths,small n regime,planar subclass,desired-grade retry or weaker replacement. Old r17 whole clique-sum scope stays unchanged. Child full source reading and incomplete transitive primary reading remain honestly distinguished. Every earlier frozen/PREFREEZE target and closed disposition remains immutable.

'''
direct = ['discovery-arithmetic-r162y-parent/assessment.md',
          'fresh-arithmetic-discovery-r162y/FINAL.md',
          'fresh-arithmetic-discovery-r162y/packet/private/prefreeze-mathematics.md',
          'fresh-arithmetic-discovery-r162y/packet/private/primary-understanding.md',
          'fresh-arithmetic-discovery-r162y/packet/private/READING-LIMITS.md']
inputs = []
for name in direct:
    path = B / name
    raw = path.read_bytes()
    inputs.append({'path': str(path.relative_to(P)), 'bytes': len(raw),
                   'mode': path.stat().st_mode, 'sha256': hashlib.sha256(raw).hexdigest()})
nav = json.loads((D / 'private/canonical-navigation.json').read_text())
catalogue = '''Catalogue access, if needed: ONLY binary seek/read sources/CONTENTS.md[149459,152756), EXACT Source090 body. Parent decoded only the first TWO numeric-bold title strings from ONE bounded14000-byte window and ONLY090 body. No child title locator,extra family,catalogue screen,ancestor hunt or whole-catalogue opening/decoding. Source091 is not selected. FOUR confirmed canonical folders have75 blobs/95 complete-tree entries including roots. Actual build/main.tex wrappers are confirmed below; one contains most of its mathematics inline and the others have operative includes. Parent source-body reading: NONE. Metadata is navigation,not proof reading.

Read these FIVE exact COMPLETED originals as narrow direct exceptions relative to frontier/campaigns/2026-10-14/:
'''
catalogue += '\n'.join(direct) + '''
These exact exceptions do not authorize containing namespaces,links,other copied/source bundles,role/brief/status/activity aliases or other peer findings. Protected completed bodies AND named metadata remain PRIVATE/local under original rights; any copies stay within your own root. No old r35,R041 or another past exact-body exception propagates. No broader old scan rerun.

'''
family = '''Your ONE developed family is SOURCE090: PLANAR TRIANGULAR-LATTICE UNIVERSAL OPTIMALITY,SHARP FOURIER PACKING CERTIFICATES,RENORMALIZED RIESZ/COULOMB AND SPHERICAL LOGARITHMIC ENERGY. All FOUR pinned manuscripts AND ALL operative source proofs are stipulated TRUE,including formerly conjectural conclusions. Validate new deductions and exact applicability; do not audit upstream truth.

Confirmed canonical folders and ACTUAL wrappers:
'''
for entry in nav['families']:
    w = entry['wrapper']
    family += f"{entry['folder']}\n{w['path']}\nbytes {w['size']}; Git blob {w['sha']}.\n"
family += '''
Authenticate ALL75 canonical blobs against complete-tree size/Git blob/SHA256,including READMEs,compiled PDFs,figures and all local objects. Read ALL FOUR actual theorem/proof bodies,operative ancestors,real nested includes and required companions supporting the developed operation,strongest relevant ACTUAL primary proofs,and eligible ORIGINAL-history sections BEFORE extended mathematical deductions or author drafting. Follow actual includes,not filename guesses. Distinguish proof reading from duplicate PDF/typography or ancillary-code authentication. Operative interval/certificate results are stipulated; do not rerun computation to audit upstream truth. Read the actual arguments to understand the stronger mechanisms they expose. Recover clipped seams and keep durable mathematical understanding with exact source labels,primary versions/URLs/read extents,access failures and unread ancestry. Metadata and others' ledgers are not proof reading. Mathematics must dominate proportionate evidence work.

The ENTIRE source universal-optimality conclusion is PAID: triangular minimality for every nonnegative completely monotone function of squared distance over the full actual class of locally finite planar configurations of centered-disk density one,including infinite energies and the exact lower-limit averaging conventions. All sharp Gaussian Fourier minorants,atomic interpolation,positive-mixture and heat-kernel mechanisms actually proved are paid. The full unit-background renormalized Riesz conclusions for 0<s<2,logarithmic/Coulomb and jellium minima,the Sandier-Serfaty result,and the BHS linear term for optimal ordered-pair logarithmic energy on the unit sphere are paid at their actual scopes and normalizations. The full planar Cohn-Elkies sharpness certificate,global sign conditions,optimal packing density and actual periodic equality classification are paid. Read exact theorem statements and full proofs before giving constants or equality claims; the catalogue does not specify every cutoff,normalization or admissible class.

Standard density dilation,energy scaling/additive renormalization constants,Tonelli/Bernstein positive mixtures,limits already controlled by the full source bounds,LP/Poisson/periodic supercell comparisons and direct asymptotic substitutions are paid wherever every hypothesis matches. A new potential restatement,another positive mixture,ordinary Gaussian-to-Riesz transfer,the already proved spherical coefficient or a periodic equality restatement is not a nominee. A quantitative defect law,relative/coherent construction,uniformity,hypothesis removal or another operation is eligible only with a CLOSED identifiable nonroutine mechanism after the strongest compatible source/primary payment. Inspect the actual source remainders,strictness,Voronoi comparisons,screening/heat interfaces and equality mechanisms; do not declare them unavailable because the headline states only minimality. A failed naive construction does not exclude stronger known compositions.

Track ordered versus unordered pair counts,half factors,Gaussian Fourier convention,density/covolume and centered disks versus translation-uniform density,liminf versus actual limits,local finiteness versus uniform separation/Delone assumptions,infinite energies and zero/constant potentials,admissible positive-mixture measures,periodic versus arbitrary configurations,and all truncation/thermodynamic orders. In long-range problems retain the SAME point configuration,background,curl-free/admissible field,cutoff,heat regularization,renormalization counterterms and boundary budget across all operations. Read exact unit-sphere conventions before comparing linear coefficients. Do not interchange independent optimizing fields/configurations or limits without a compatible proof.

Equality in an averaged energy does not by itself imply one globally prescribed triangular lattice: zero-density changes and coherent orientation/translation requirements must be addressed at the full claimed scope. Strictness of one Gaussian term does not silently settle every degenerate nonnegative potential. Periodic equality classification cannot be imported as an all-configuration rigidity theorem. A stability claim must specify its metric/topology,which common lattice/field/normalization it uses,and treatment of boundary/defect densities; merely proving local pair slack or qualitative compactness already available from the source is not automatically substantial.

Do not replace a proposed FULL scope by periodic lattices,Bravais-only configurations,uniform separation,bounded holes,finite boxes with favorable boundary,tame fields,special potentials,a fixed Gaussian parameter,restricted s,a favorable sequence of radii or an unproved compactness/screening assumption. Preserve all earlier frozen/PREFREEZE scopes,including full graph-metric/projection-body diagnostics and closed R162W. On mechanism overlap read eligible ACTUAL original-history sections under the prospective guards; exact completed exceptions never open linked protected namespaces.

After complete operative reading,choose and develop ONE distinct fully specified full-scope operation through sustained CONCRETE mathematics beyond a first failed shortcut. Try the strongest integrated source/primary payment before calling a bridge unpaid. Keep actual configurations,shared witnesses,parameter/defect/energy/boundary budgets and every compatibility step. Preserve paid calculations,failed attempts and precise residuals. If a viable theorem emerges,freeze exact hypotheses,all quantifiers/constants and conclusion BEFORE author-proof development,then close every interface. Otherwise honest PREFREEZE/no nominee with exact gaps; no weaker substitute,self-grade,count,exhaustive clearance,global impossibility or priority claim. A difficult unproved target is not a finding.

Keep source/primary/history/search/extract/render/copied bodies AND their named metadata PRIVATE/local under original rights. Serialize EVERY literal wildcard/substring rule below before optional filename traversal or body selection beyond the exact direct exceptions,retaining all r/no-r,flat/compound/role aliases. At most ONE correctly pruned original-history traversal,without size/extension cutoff on eligible authored UTF8 after pruning;no projectwide rg-then-filter,broad untracked inventory or old scan rerun. Disclose false admissions,coarse omissions,versions/read extents,truncation recovery,late reads and incomplete transitive ancestry. Seal YOUR own fresh exact selection ONCE at the end with detached FINAL/MANIFEST/outside REPORT hashes,a read-only explicit-anchor verifier and proportionate tiny COPIED own-text controls. No inherited manifest over fewer files. Artifact checks are not math gates. No nested agents,shared/git writes,public/browser actions or downstream formal/manuscript/release work. Parent alone commissions independent correctness and separate actual-primary substantial-contribution reviews of a viable full author proof.

'''
text = prefix + previous + catalogue + family + isolation + '\nFurther prospective literal twins:\n*arithmetic*162z* *arithmetic*r162z*\n\n' + marker.decode() + standing.decode()
assert set(re.findall(r'\*[^\s,;()]*\*', old)) <= set(re.findall(r'\*[^\s,;()]*\*', text))
assert text.encode().split(marker, 1)[1] == standing
brief = B / 'expanded-target-2026-10-17/fresh-arithmetic-r162z-brief.txt'
assert not brief.exists() and not list((B / 'fresh-arithmetic-discovery-r162z').iterdir())
brief.write_text(text)
(D / 'private/completed-direct-inputs.json').write_text(json.dumps(inputs, indent=2) + '\n')
record = {'brief': str(brief.relative_to(P)), 'bytes': len(text.encode()),
          'sha256': hashlib.sha256(text.encode()).hexdigest(), 'standing_bytes_preserved': 5570,
          'all_previous_literal_guards_retained': True, 'source': '090',
          'catalogue_extent': [149459,152756], 'canonical_blobs': 75,
          'canonical_entries_including_roots': 95, 'completed_direct_inputs': 5,
          'parent_source_body_read': False, 'publication': 'STOPPED'}
(D / 'brief-preparation.json').write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record))
