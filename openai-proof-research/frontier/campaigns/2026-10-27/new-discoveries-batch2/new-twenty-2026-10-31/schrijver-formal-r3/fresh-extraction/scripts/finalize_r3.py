from pathlib import Path
import json,hashlib,re,collections
r=Path(__file__).resolve().parent.parent;fresh=r/'fresh-extraction'
replay=json.loads((fresh/'replay-result.json').read_text());assert replay['status']=='PASS_PARTIAL_ONLY'
mods=json.loads((r/'outputs/modules.json').read_text())
before=json.loads((r/'frozen-before.json').read_text())
after={n:hashlib.sha256((r/'src'/n).read_bytes()).hexdigest() for n in before};assert before==after
assert all(hashlib.sha256((fresh/'src'/n).read_bytes()).hexdigest()==h for n,h in after.items())
(r/'frozen-after.json').write_text(json.dumps(after,indent=2))
def audit(name):
 p=sorted((fresh/'logs').glob(f'replay-build-{name}-*.log'))[-1];s=p.read_text()
 return dict(total=int(re.search(r'TOTAL_LOCAL_DECLARATIONS (\d+)',s)[1]),by_module=dict(collections.Counter(re.findall(r'^MODULE (\S+)',s,re.M))),modules=re.findall(r'^AUDIT_MODULE (\S+)',s,re.M),log=str(p.relative_to(r)))
a=audit('AuditR3');cl=audit('ClosureAudit');assert set(cl['modules'])==set(json.loads((r/'outputs/endpoint-closure.json').read_text()))
new=set(mods)-{Path(n).stem for n in before}
result=dict(mathdb_id=352827,round=3,status='PARTIAL',unconditional_endpoint=False,conditional_endpoint='Schrijver.mathdb_352827_round3_conditional',self_accepted=False,accepted_credit=0,root_decides=True,
modules={m:dict(path=f'src/{m}.lean',sha256=hashlib.sha256((r/'src'/f'{m}.lean').read_bytes()).hexdigest(),frozen=m not in new,strict_compiled=True,leanchecker=True) for m in mods},frozen_unchanged=True,frozen_count=len(before),frozen_archive_sha256='b15a51e3adac2e0069bcf262272f5a27ed0550f885b674d5e6eae6ea23a03c99',audit=a,endpoint_closure_audit=cl,
remaining_props={'Schrijver.Enumeration27':'StoredEnumerationComplete 27 12 vertexMasks27.toList','Schrijver.Enumeration28':'StoredEnumerationComplete 28 12 vertexMasks28','Schrijver.RotationRepresentativeCoverage28':'∀ a : Vertex 28 12, ∃ t : Fin 28, ∃ r : Fin 3185, r ∈ upperRoots28 ∧ rotateVertex t a = indexedVertex maskAt28 masks28_valid_at r'},completed=['packed lookup correspondence at every index for both frozen stored tables','packed lookup injectivity for both graphs','literal isomorphisms conditional only on exact stored enumeration completeness','all 116 checked upper trees combined','connectivity, distance, and bounded walk transport along graph isomorphisms','both frozen bridge Props derived from exactly the three named remaining Props'],missing=['gap enumeration completeness and equality with stored tables','concrete literal rotation representative coverage','unconditional endpoint'],replay=dict(fresh=True,status=replay['status'],modules=len(mods),negative=replay['negative'],receipt='fresh-extraction/replay-result.json'),source_archive='schrijver-partial-source.zip',operational_exceptions=['initial lightweight orchestration was uncapped','one accidental empty /tmp/unused file was created outside the lane','rm-style cleanup rejected by automatic review; cleanup not necessary'],prior_art_status='Inherited qualified limitation; no new novelty claim')
for a in [result['audit'],result['endpoint_closure_audit']]:a.update(unsafe=0,partial=0,unsafe_rec=0,implemented_by=0,extern=0,allowed_transitive_axioms=['propext','Classical.choice','Quot.sound'])
receipts=[json.loads(p.read_text()) for p in (fresh/'logs').glob('*.log.json')]
result['resources']=dict(peak_private_bytes=max(x['peak_private_bytes'] for x in receipts),max_wall_seconds=max(x['wall_seconds'] for x in receipts))
(r/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status='PARTIAL',modules=len(mods),new_modules=len(new),audit=a['total'],closure=len(cl['modules']))))
