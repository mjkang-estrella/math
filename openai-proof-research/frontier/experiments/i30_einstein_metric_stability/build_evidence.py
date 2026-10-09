#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,re,html
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i30_einstein_metric_stability'
P='frontier/sources/i27_geometric_analysis_discovery/pinned/preprints/'
EG=P+'An-L2-Einstein-Gap-for-Nonnegatively-Curved-Four-Manifolds-October-5-2026/build/source/main.tex'
E0=P+'Zero-Plane-Rigidity-for-Einstein-Four-Manifolds-October-4-2026/build/sections/'
EP=P+'Positively-curved-Einstein-four-manifolds-September-23-2026/build/sections/'
L='frontier/sources/i30_einstein_metric_stability/literature/'
passages=[]
def passage(path,start,end,why):
 b=(R/path).read_bytes();lines=b.splitlines(keepends=True);end=min(end or len(lines),len(lines));p=b''.join(lines[start-1:end]);passages.append(dict(path=path,start=start,end=end,sha256=hashlib.sha256(p).hexdigest(),file_sha256=hashlib.sha256(b).hexdigest(),purpose=why))
passage(EG,1,None,'Full EG manuscript, including all proofs; stipulated truth, not upstream audit.')
for file,end,why in [('01-introduction.tex',None,'Exact boundary and full nonnegative classification contracts'),('02-preliminaries.tex',125,'Einstein curvature blocks and divergence-free identity; direct-route obstruction'),('06-coupling.tex',330,'Combined derivative identities, integrand bounds, and start of quartic proof'),('08-classification.tex',None,'Complete equality-case/parallel-block/splitting proof')]:passage(E0+file,1,end,why)
passage(EP+'01-introduction.tex',1,95,'Classification statement, previous scope and Weyl-block setup')
passage(EP+'08-classification.tex',1,None,'Complete strongest classification proof including model scaling')
for name,spans,why in [
 ('1202.2912v1.txt',[(1,125),(999,1050),(1165,1810)],'TW exact flow convention, pseudolocality assumptions, tensor error, full distance/volume packing proof'),
 ('2102.12840v3.txt',[(35,220),(1220,1305),(1360,1378)],'CCL smoothing, compactness and metric topology comparison, exact HKRX citation'),
 ('2408.11115v2.txt',[(1,220)],'Martens exact hypotheses and Remark 1.3 time-zero limitation'),
 ('1808.03774v1.txt',[(365,525)],'HKRX available preprint: pseudolocality/Reifenberg and short-range time-zero comparison'),
 ('2008.09956v2.txt',[(1330,1395)],'HW Appendix A exact data and coarse packing argument'),
 ('2109.02449v1.txt',[(2240,2390)],'MW Lemma 5.1 antecedent, exact supercritical and volume assumptions'),
 ('1312.2224v2.txt',[(1140,1230)],'Kroncke entropy gradient and conditional dynamical statements'),
 ('Koiso1982.txt',[(150,210),(790,850)],'Einstein deformation operator, compact symmetric-space rigidity'),
 ('GV2015.txt',[(2368,2485)],'Exact CP2 TT spectral normalization and equal product spectral proof')]:
 for lo,hi in spans:passage(L+name,lo,hi,why)
contracts=[
 dict(source='EG',labels=['prop:initial','prop:initial-sobolev'],input='closed connected simply connected sec>=0 four-manifolds; D -> 0; average scalar normalized to 12',output='universal volume/diameter/Sobolev; ||Ric-3g||_2^2 <=5D'),
 dict(source='EG',labels=['prop:tail','lem:noncollapse','prop:smoothing','prop:einstein-defect'],input='same class; sufficiently small D',output='common [0,T], R>=0, Sobolev and noncollapse, |Rm|<=A/t, quantitative Gronwall ||L(t)||_2<=C sqrtD'),
 dict(source='EG',labels=['prop:sectional-defect','prop:limit'],input='sequence in normalized class D->0',output='after fixed diffeomorphisms smooth positive-time convergence to (1-6t)h; Ric_h=3h, sec_h>=0; no original-distance assertion'),
 dict(source='E0',labels=['thm:main','cor:nonnegative-classification','prop:constant-norms','prop:parallel-blocks'],input='closed connected exact Ric=3g, sec>=0',output='one zero plane forces universal-cover equal sphere product; all nonnegative models classified'),
 dict(source='E+',labels=['thm:classification','prop:parallel-models','lem:model-curvature','lem:global-isometry'],input='closed connected Einstein, sec>0, no orientation assumption',output='round S4/RP4 or FS CP2 up to scaling; model CP2 Ric3 is twice unit-Hopf metric'),
 dict(source='GV',labels=['Proposition 7.7','Proposition 7.9'],input='CP2 Ric6 and equal S2 product Ric1, TT tensors',output='-Delta_L bottom32 for CP2; product spectrum0 then >=4. After Ric3 scaling:16 and {0} union [12,infty).'),
 dict(source='TW',labels=['Theorem 3.1','Lemma 4.4','Theorem 4.1'],input='normalized flow -Ric+lambda0g, |lambda0|<=1, initial Ric lower and almost Euclidean unit-ball volume',output='power distance estimates from spacetime scalar error; existing missing-ball and packing mechanism; not directly applied with its unproved local volume premise here')]
(S/'contracts.json').write_text(json.dumps(dict(contracts=contracts,read_passages=passages),indent=2)+'\n')
versions=[]
for p in sorted((S/'literature').glob('*abs.html')):
 txt=p.read_text();a=txt.find('Submission history');b=txt.find('<div',a)
 # Preserve complete submission history block up to the next section div.
 excerpt=txt[a:a+5000];end=excerpt.find('<div')
 if end>=0:excerpt=excerpt[:end]
 text=html.unescape(re.sub('<[^>]*>',' ',excerpt));text=' '.join(text.split())
 versions.append(dict(path=str(p.relative_to(R)),submission_history=text))
(S/'primary-versions.json').write_text(json.dumps(versions,indent=2)+'\n')
queries=[
 ['Ricci flow distance distortion initial Ricci lower bound small curvature concentration Chan Chen Lee 2102.12840','Ricci flow distance distortion Lp Ricci initial metric trace nonnegative sectional curvature Simon Topping higher dimensions'],
 ['Huang Kong Rong Xu Collapsed manifolds Ricci bounded covering geometry Lemma 2.4 distance Ricci flow','almost Einstein metrics nonnegative sectional curvature quantitative Gromov Hausdorff L2 stability','Einstein metrics Lojasiewicz inequality Ricci tensor distance Einstein metric integrability S2 S2 CP2'],
 ['"Ricci flow" "distance distortion" "initial" "Ricci lower" Huang','"almost Einstein" "Gromov" "quantitative" Tian Wang','"Einstein" "local rigidity" "S2" "Koiso"'],
 ['site.arxiv.org "On the structure of almost Einstein manifolds"','site.arxiv.org "Ricci curvature integrals, local functionals"','site.arxiv.org "Stability of Einstein metrics under Ricci flow" Kröncke','site.arxiv.org "Collapsed Manifolds With Ricci Bounded Covering Geometry"'],
 ['"S2 × S2" "infinitesimal Einstein"','"S^2" "S^2" "Einstein deformations" rigidity','Koiso "Non-deformability" Einstein metrics PDF','site.arxiv.org Kröncke "On the stability of Einstein manifolds"'],
 ['site.arxiv.org Gursky Viaclovsky "Rigidity and stability" quadratic','site.ams.org "Collapsed manifolds with Ricci bounded covering geometry" pdf','site.ams.org "On the structure of almost Einstein manifolds" pdf'],
 ['"Ricci flow" "distance distortion" "2026" Ricci lower bound','"almost Einstein" "nonnegative sectional" stability metric','"Ricci flow" "distance distortion" "initial" "L2"']]
(S/'queries.json').write_text(json.dumps({'date':'2026-10-09','batches':queries,'retained_result_batches':[3,4,5,6,7],'note':'Initial two exploratory result bodies not separately archived; exact queries retained. Primary documents are all byte-retained with manifest hashes. Search absence is not priority evidence.'},indent=2)+'\n')
print(len(contracts),'contracts;',len(passages),'read passages;',len(versions),'version histories')
