from pathlib import Path
import json,hashlib,re,collections,zipfile
R=Path(__file__).resolve().parent; B=R.parent
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
raw=(R/'ReviewAudit.stdout').read_text()
items=[]
for m in re.finditer(r'AUDIT (\S+) (\S+)\nTYPE (.*?)\nAXIOMS (.*?)\nFLAGS unsafe=(\w+) partial=(\w+) axiom=(\w+)',raw,re.S):
 mod,name,typ,axs,u,p,a=m.groups(); assert '…' not in typ and '...' not in typ; assert (u,p,a)==('false','false','false'); axioms=re.findall(r'[\w.]+',axs); assert set(axioms)<={'propext','Classical.choice','Quot.sound'}
 items.append(dict(module=mod,name=name,type=typ,axioms=axioms,unsafe=False,partial=False,axiom=False))
assert len(items)==205 and 'AUDIT_TOTAL 205' in raw
(R/'declaration-audit.json').write_text(json.dumps({'count':len(items),'modules':dict(collections.Counter(x['module'] for x in items)),'pp.proofs':True,'pp.explicit':True,'declarations':items},indent=2))
# Fresh dependency provenance, without git commands.
P=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages')
prov={}
for p in sorted(P.iterdir()):
 cache=p/'.lake/build/lib/lean'
 if not cache.is_dir():continue
 g=p/'.git'
 if g.is_file():g=(p/g.read_text().strip().removeprefix('gitdir: ')).resolve()
 head=(g/'HEAD').read_text().strip(); head=(g/head[5:]).read_text().strip() if head.startswith('ref: ') and (g/head[5:]).exists() else head
 prov[p.name]={'head':head,'cache':str(cache),'objects':{str(x.relative_to(cache)):H(x) for x in sorted(cache.rglob('*.olean'))}}
assert prov['mathlib']['head']=='d13f23b723b8a846827a245b89c10fc7d3f11612'
lean=Path('/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean')
(R/'dependency-provenance.json').write_text(json.dumps({'packages':prov,'binaries':{str(x):H(x) for x in [lean,lean.parent/'leanchecker']},'trust':'Cached upstream objects trusted, consumed without writes; not source-to-object attestation or independent verifier.'},indent=2))
refs=[]
for rel,url,label,depth in [
('expanded-corpus-r40/raw/347913.jsonl','https://mathdb.com/p/347913/convexity-conjecture-for-the-hypergraph-based-polynomial-f-d','frozen r40 literal record','full record'),
('expanded-corpus-r40/sources/2009.04510','https://arxiv.org/pdf/2009.04510v1','arXiv v1','definition Eq2 and Sec3 Conj1, cached extracted body read'),
('expanded-corpus-r40/sources/published-brosch','https://doi.org/10.1137/20M1369592','SIAM 2021 version of record','Eq1.1 and Sec4 Conj1 p2242, cached extracted body read'),
('ordinary-candidates-source-review-r1/polak-published.body','https://ir.cwi.nl/pub/31516/31516.pdf','arXiv2104.08264v2, despite cache filename','Theorem1.1 and Section2 reduction/proof context read'),
('ordinary-candidates-source-review-r1/queue-citer.body','https://arxiv.org/pdf/2111.05777','arXiv2111.05777v2','coefficient formula, Theorem1, Lemma3 proof, Corollary1 discussion read'),
('ordinary-candidates-source-review-r1/thesis-brosch.body','https://www.danielbrosch.com/assets/pdfs/Thesis.pdf','2022 Tilburg thesis','Chapter5 Conj5.17 and Hessian reduction context read')]:
 p=B/rel;refs.append(dict(path=str(p),sha256=H(p),url=url,version=label,read_depth=depth))
(R/'source-reference-index.json').write_text(json.dumps({'references':refs,'classical_antecedent':{'DOI':'10.1080/01621459.1967.10482885','read_depth':'1967 full mgf body unread in completed review'},'qualifications':['2025 quantum-channel citing body unread in completed review','No complete earlier subsumer demonstrated by bounded completed review; conditional only','Active focused significance review pending and unread; no current verdict inferred'],'copied_review_provenance':{str(p.relative_to(R)):H(p) for p in (R/'reviews').rglob('*') if p.is_file()}},indent=2))
scan={str(p.relative_to(R)):re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|ofReduceBool)\b',p.read_text()) for p in (R/'replay/extracted/src').rglob('*.lean')}
# Audit code mentions flags; source scanning is a diagnostic, actual environment audit decisive.
(R/'source-scan.json').write_text(json.dumps(scan,indent=2))
f=json.loads((R/'frozen-inputs.json').read_text());bad=[p for p,h in f.items() if H(Path(p))!=h];assert len(f)==178 and not bad
(R/'bindings-after.json').write_text(json.dumps({'count':178,'mismatches':bad,'all_unchanged':True},indent=2))
build=json.loads((R/'replay/build/build.json').read_text());assert len(build)==36 and all(x['exit']==0 for x in build)
result={'mathdb_id':347913,'status':'DRAFT_COMPLETE_ROOT_ACCEPTANCE_PENDING','endpoint':'PolynomialConvexity.source_conjecture : PolynomialConvexity.SourceConjecture','fresh_strict_builds':18,'fresh_leanchecker_modules':18,'local_origin_declarations':205,'mathematical_modules':17,'full_types_without_ellipsis':True,'allowed_axioms':['propext','Classical.choice','Quot.sound'],'negative_controls':json.loads((R/'controls.json').read_text()),'frozen_bindings_unchanged':178,'lean_files_preserved_byte_identically':18,'archive_sha256':H(R/'proof-source-only.zip'),'novelty':'Focused significance review ACTIVE/PENDING; unfinished outputs not read. Retain completed ordinary review conditional qualifications.','root_acceptance':'PENDING','accepted_credit':0,'helper_credit':0,'campaign_context':'3/20 beyond 39','jobs_remaining':0,'trust':'Trusted upstream package caches; same-kernel leanchecker, no full upstream attestation.'}
(R/'results.json').write_text(json.dumps(result,indent=2))
print('205 complete types; 36 build/check receipts; 178 frozen bindings PASS; dependency hashes recorded')
