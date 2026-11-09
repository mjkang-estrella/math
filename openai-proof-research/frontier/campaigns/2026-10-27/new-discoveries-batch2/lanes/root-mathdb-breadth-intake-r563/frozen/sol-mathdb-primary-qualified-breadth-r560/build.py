import pathlib,json,hashlib,datetime,itertools
D=pathlib.Path(__file__).parent
A=json.loads((D/'assigned-records.json').read_text());notes={}
for line in (D/'assessments.tsv').read_text().splitlines():
 i,s,n=line.split('\t');notes[int(i)]=(s,n)
assert len(notes)==50
out=[]
for a in A:
 r=a['record'];i=r['mathdb_id'];s,n=notes[i]
 out.append({'mathdb_id':i,'disposition':s,'assessment':n,'literal_statement':r['statement'],'statement_sha256':a['statement_sha256'],'canonical_record_sha256':a['canonical_record_sha256'],'corpus_chunk':a['chunk'],'corpus_line':a['line'],'source_url':r['source_url'],'canonical_url':r['canonical_url'],'statement_review':'complete_literal_with_quantifiers','primary_passage_read':i in [328279,333786],'successor_theorem_body_read':i in [333786,334590],'whole_body_read':False,'full_dependency_audit':False,'current_registry_cleared':False,'novelty_cleared':False,'accepted_credit':0})
(D/'dispositions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');(D/'proposals.json').write_text('[]\n')
# One exact illustration of known source refutation; no sweep or novelty claim.
E=[(0,2),(0,3),(1,2),(1,3),(1,4),(2,4),(3,4)];deg=[sum(v in e for e in E) for v in range(5)];irr=sum(abs(deg[i]-deg[j]) for i in range(5) for j in range(i));assert sorted(deg)==[2,3,3,3,3] and irr==4
calc={'id':328279,'executed':True,'edges':E,'degrees':deg,'total_irregularity':irr,'conjectured_lower_bound':6,'interpretation':'Small parameter instance of source-known refutation; zero credit; connected by paths through vertices2 and1.'}
(D/'calculation-results.json').write_text(json.dumps(calc,indent=2)+'\n')
prov={'coverage':{'literal_statements':50,'primary_question_passages':2,'source_internal_local_theorem_proofs':1,'successor_local_theorem_bodies':2,'whole_bodies':0,'full_dependency_audits':0,'registry_clearances':0,'proposals':0},'sources':json.loads((D/'downloads.json').read_text())+json.loads((D/'downloads2.json').read_text()),'passage_scope':{'328279':'1407.1276v1 Conjecture1.1, Theorem2.1 and local proof; no full audit of Lemmas2.1/2.2; HTML local proof appears to print n(n-y) where degree count gives y(n-y); not relied on for numerical certificate.','333786':'1608.03934v2 definition of positive-integer lecture-hall polytope and Conjecture5.1. 1911.12459v1 Theorem1 and full local proof; chain specialization exact normalized coordinate inequalities. Other algebraic/triangulation sections not read.','334590':'1906.03991v2 Theorems2.8 and3.1, local injectivity proof and implication from known triangular tropical identities. Lemma2.4/2.7 and external identity dependencies not fully audited. Original-question HTML unavailable.'},'chronology_limit':'HTML labels arXiv versions but generated date in1911.12459v1 is August24,2026. Bytes and URL pinned; no PDF/version equivalence independently checked. No universal publication-priority claim.','searches':[{'queries':['total irregularity 2n-4 conjecture non regular','lecture hall polytopes integer decomposition arbitrary sequences','plactic monoids identities finite rank proved','strongly Tutte-descriptive conjecture inactive'],'primary_leads':['https://arxiv.org/abs/1407.1276','https://arxiv.org/abs/1911.12459','https://arxiv.org/abs/1906.03991'],'utc_date':'2026-10-31','scope':'Search results are routing leads only, not proof-body clearance.'}],'registry':'Unavailable per assignment; HOLD. No MathDB requests. No absence-of-hits inference.'}
(D/'source-provenance.json').write_text(json.dumps(prov,indent=2)+'\n')
# Include downloaded source and derivative pins in flat bindings.
b=json.loads((D/'flat-bindings.json').read_text())
for e in prov['sources']:
 if 'path' in e:b.append({k:e[k] for k in ['path','sha256','size']})
b+=json.loads((D/'derivative-bindings.json').read_text())
(D/'flat-bindings.json').write_text(json.dumps(b,indent=2)+'\n')
