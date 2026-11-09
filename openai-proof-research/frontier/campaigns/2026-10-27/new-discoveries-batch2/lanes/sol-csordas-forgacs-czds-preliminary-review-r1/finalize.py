from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
bindings=json.loads((L/'bindings.json').read_text())
for b in bindings:
 assert h(L/b['copy'])==b['sha256']
 if b['kind']=='scientific':assert h(Path(b['original']))==b['sha256']
coverage={
 '02-1505.00355v2.txt':{'lines':[[86,113],[1250,1298],[1414,1418]],'coverage':'Definition4, Proposition35 proof outline, Problems36–37 and closest citation; not full-paper proof audit'},
 '03-craven1995-correct.txt':{'lines':[[1,340],[550,615]],'coverage':'Definitions1.3/1.5, Remark1.6, Theorem1.7, reciprocal-necessity paragraph, Example1.8; Theorem2.13 and proof; partial early Section2; not entire paper'},
 '17-2312.09482.txt':{'lines':[[1,23],[90,130],[500,550],[640,692]],'coverage':'coding statements plus actual Theorem4.6 proof and Corollary4.10 proof'},
 '22-1511.08080.txt':{'lines':[[1,23],[450,491]],'coverage':'Krull conjecture and surrounding known bounds; cited original zero-sum proofs not separately read'},
 '26-1408.0142.txt':{'lines':[[1,23],[245,286]],'coverage':'polling conjecture and mechanism/obstruction discussion; Poisson original proof not independently audited'},
 '28-1407.2380.txt':{'lines':[[1,23],[324,355]],'coverage':'Zaremba/Moser statements and discrepancy bridge; no current resolution claim'},
 '15-2304.10570.txt':{'lines':[[1,23],[118,165],[190,217]],'coverage':'tensor Problems1–6 context; selected Problem4; no cited monograph proof audit'},
 '09-2308.04072.txt':{'lines':[[1,23],[555,640]],'coverage':'Hardy norm statements, Lemma5.3 actual dilation proof; other cited norm proofs not audited'},
 '13-2303.00699.txt':{'lines':[[1,35],[150,248],[566,615]],'coverage':'lattice representation construction discussion, characterization question, necessary-condition boundary, patch specialization'},
 '46-source-version.html':{'coverage':'submission/revision chronology and DOI metadata only'},
 '00-PROOF.md':{'coverage':'entire candidate argument read; finite RouteA independently certified; analytic RouteB read but not used/certified'},
 '01-moment-witness.json':{'coverage':'entire rational data parsed; r, epsilon, negative_form, input, output and input_at_one independently checked'}
}
for name,data in coverage.items():data['sha256']=h(L/'frozen'/name)
(L/'body-coverage.json').write_text(json.dumps({'read':coverage,'other_frozen_files':'custody only unless a duplicate of a listed body; not full-body coverage or novelty clearance'},indent=2)+'\n')
provenance={
 'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'role':'solo independent preliminary review; no children',
 'assigned_lane':str(L),'freeze':'bindings.json; scientific originals and copies verified before body reading and after review; administrative snapshots only',
 'source_urls':{'2015v2':'https://arxiv.org/pdf/1505.00355v2','1995':'https://intlpress.com/site/pub/files/_fulltext/journals/maa/1995/0002/0004/MAA-1995-0002-0004-a004.pdf'},
 'source_chronology':{'1995':'Methods Appl Anal2(4),420–441; received1994-11-12 revised1995-05-03','2015v1':'2015-05-02T16:59:22Z','2015v2':'2015-08-26T18:45:54Z','certificate_and_review':'2026-10-30'},
 'retrieval':'reused hash-bound same-day primary evidence; no new requests; original access timestamps/statuses retained in administrative provenance.json and access.jsonl',
 'guard':'../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',
 'limits':{'address_space_bytes':536870912,'group_RSS_bytes':536870912,'CPU_seconds':210,'wall_seconds':230,'OPENBLAS_NUM_THREADS':1,'OMP_NUM_THREADS':1,'PYTHONDONTWRITEBYTECODE':1,'cap_raises':False},
 'checker_independence':'no worker/root checker read or imported; direct Fraction convolution and integer Bareiss',
 'observed_runs':{'freeze':{'guard_exit':0,'sampled_peak_group_RSS':20656128},'schema':{'guard_exit':0,'sampled_peak_group_RSS':9797632},'exact':{'guard_exit':0,'sampled_peak_group_RSS':19111936,'guard_wall_seconds':0.6411673770053312},'determinants':{'guard_exit':0,'sampled_peak_group_RSS':15867904,'guard_wall_seconds':1.2026707630138844},'administrative_read':{'guard_exit':0,'sampled_peak_group_RSS':10059776}},
 'gates':{'SOURCE':'arXiv PASS / journal HOLD','MATH':'PASS exact finite witness','SUBSTANTIVE':'recommend EXCLUDE routine source/classical adaptation','NOVELTY':'prior publication unresolved; bounded gaps retained','FORMAL_FEASIBILITY':'feasible finite route; no Lean/build audit'},
 'credit':0,'root_alone_accepts_and_counts':True,'counts':{'additional':9,'total':39,'next':40},
 'limitations':['No current registry head clearance; inherited challenges parked','No journal body comparison','No comprehensive citing-literature/MathSciNet/zbMATH clearance','RouteB analytic uniqueness not independently certified; not relied upon'],
 'prohibited_actions_performed':False,
}
(L/'provenance.json').write_text(json.dumps(provenance,indent=2,ensure_ascii=False)+'\n')
files={str(p.relative_to(L)):{'sha256':h(p),'bytes':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
(L/'MANIFEST.json').write_text(json.dumps({'algorithm':'SHA-256','excludes':['MANIFEST.json','verification-receipt.json'],'files':files},indent=2)+'\n')
print({'manifest_files':len(files),'scientific_bindings_unchanged':True})
