import pathlib,json,hashlib,datetime
D=pathlib.Path(__file__).resolve().parents[1];p=D/'results.json';x=json.loads(p.read_text());extra={'336735':['optical-proof'],'337903':['edge-proof'],'337871':['hypercube-correct'],'339273':['old-univalent-abs','old-univalent-v1','univalent-abs','univalent-v1','univalent-v2'],'355321':['pinkus-primary','old-covariance-abs','old-covariance-v1','old-covariance-v2'],'381367':['rsystem-vor'],'337877':['flip-followup','pseudocircle-vor'],'336863':['expansion-vor'],'337428':['torus-author'],'337070':['hom-vor'],'337704':['cordial-vor']}
for i,names in extra.items():
 for name in names:
  q=D/f'sources/{name}.receipt.json'
  if q.exists():x[i]['source_receipts'][str(q.relative_to(D))]=json.loads(q.read_text())
p.write_text(json.dumps(x,indent=2,ensure_ascii=False)+'\n')
rp=D/'outputs/registry-screen.json';r=json.loads(rp.read_text());r['registries']['omega']['selected_topic_metadata_read']={'path':'Problems/krop-mittal-wigal-2024-game-cordiality-tree-path.md','local':'sources/omega-cordial-topic.body','assessment':'Two-player minimax game cordiality on ordinary trees; different from existential k-cordial hypertree labeling. No implication to the reserved statement established.'};rp.write_text(json.dumps(r,indent=2)+'\n')
errors=[];rs=json.loads((D/'reservation.json').read_text());assert set(x)=={str(i) for i in rs['ids']}
for i,row in x.items():
 raw=(D/f'raw/{i}.jsonl').read_bytes();assert raw.endswith(b'\n');assert hashlib.sha256(raw).hexdigest()==row['provenance']['raw_sha256'];assert hashlib.sha256(row['literal_statement'].encode()).hexdigest()==row['provenance']['statement_utf8_sha256']
for q in (D/'sources').glob('*.receipt.json'):
 rec=json.loads(q.read_text());b=q.with_name(q.name.replace('.receipt.json','.body'))
 if 'sha256' in rec:
  if not b.exists() or hashlib.sha256(b.read_bytes()).hexdigest()!=rec['sha256']:errors.append(str(q))
h=json.loads((D/'outputs/hypertrees-corrected-11.json').read_text());assert len(h)==70 and not any(v['failures'] for v in h)
k=json.loads((D/'outputs/kneser.json').read_text());assert len(k)==25 and not any(v['colorable'] for v in k)
assert not errors
report={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exactly20_reserved_results':True,'raw_and_statement_hashes':True,'all_http_body_hashes_match_receipts':True,'hypertree_corrected_cases':len(h),'kneser_cases':len(k),'nominated':0,'lean_invocations':0,'status':'bounded pass; gaps explicitly parked, no complete-literature/novelty clearance'}
(D/'outputs/delivery-validation.json').write_text(json.dumps(report,indent=2));print(report)
manifest={str(q.relative_to(D)):{'bytes':q.stat().st_size,'sha256':hashlib.sha256(q.read_bytes()).hexdigest()} for q in D.rglob('*') if q.is_file() and q.name!='evidence-manifest.json' and '/tmp/' not in str(q)}
(D/'outputs/evidence-manifest.json').write_text(json.dumps(manifest,indent=2))
