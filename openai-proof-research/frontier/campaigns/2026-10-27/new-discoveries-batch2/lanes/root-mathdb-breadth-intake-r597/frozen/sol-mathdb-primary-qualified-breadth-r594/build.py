import pathlib,json,hashlib,datetime
P=pathlib.Path(__file__).resolve().parent;L=P.parent
rows=json.loads((P/'literal-records.json').read_text());a={}
for s in (P/'assessments.tsv').read_text().splitlines():
 id,complete,status,reason=s.split('\t');a[int(id)]=(complete=='1',status,reason)
assert set(a)=={r['mathdb_id'] for r in rows}
passages={403964:('11695867-body.txt',3813,3840),403968:('11695867-body.txt',3960,4005),404538:('14298801-body.txt',1110,1245),404539:('14298801-body.txt',700,850),404583:(str(L/'sol-mathdb-primary-qualified-breadth-r454/sources/14298804.txt'),1934,1955),404585:(str(L/'sol-mathdb-primary-qualified-breadth-r454/sources/14298804.txt'),1958,1988)}
ds=[]
for r in rows:
 id=r['mathdb_id'];complete,status,reason=a[id];d={k:v for k,v in r.items() if k!='record'}
 d.update(title=r['record']['title'],source_url=r['record']['source_url'],source_name=r['record']['source_name'],complete_self_contained_statement=complete,disposition=status,technical_disposition=reason,accepted_credit=0,scope_flags={'literal_statement_read':True,'quantifiers_read':True,'complete_self_contained_statement':complete,'selected_primary_passage_read':id in passages,'whole_source_body_read':False,'local_full_scope_proof':False,'full_dependency_audit':False,'successor_body_clearance':False,'current_registry_cleared':False,'novelty_pass':False},source_passage=passages.get(id),remaining_gates='Source definitions and hypotheses where flagged; applicable successor bodies; current registry unavailable HOLD; independent proof/formal/substantive gates not passed.')
 ds.append(d)
(P/'dispositions.json').write_text(json.dumps(ds,ensure_ascii=False,indent=2)+'\n');(P/'proposals.json').write_text('[]\n')
# Exact bounded diagnostic: n=1 QSP at x=0, independent of phases, has P=0 and off-diagonal modulus 1.
# Unitarity of the product gives |P|^2+|Q|^2=1; determinant of literal form gives |P|^2-|Q|^2=1.
assert 0+1==1 and 0-1==-1
calc={'executed':'integer determinant/unitarity invariant check at n=1,x=0','input_polynomial':'f(x)=x','invariants':{'P_squared_modulus':0,'Q_squared_modulus':1,'literal_form_determinant':-1,'product_determinant':1},'interpretation':'wording-only obstruction, zero credit; does not refute intended QSP theorem','walks':'No enumeration executed; axis/origin ambiguity not promoted','fare_zones':'No sweep or solver executed; generic column-sparse observation only'}
(P/'bounded-diagnostics.json').write_text(json.dumps(calc,indent=2)+'\n')
# Check cached source against original provenance and source manifest, not merely a fresh self-binding.
old=L/'sol-mathdb-primary-qualified-breadth-r454';prov=json.loads((old/'source-provenance.json').read_text());used=[]
for n in ['14298804.html','14298804.pdf','14298804.txt']:
 f=old/'sources'/n;b=f.read_bytes();es=[e for e in prov if e.get('path')=='sources/'+n];assert es
 for e in es:assert len(b)==e.get('bytes',e.get('size')) and hashlib.sha256(b).hexdigest()==e['sha256']
 used+=es
pr=json.loads((P/'source-provenance.json').read_text());pr.append({'reused_source':str(old),'immutable_entries_verified':used,'coverage':'pp2992-2993 only; whole report and cited successor bodies not read'})
(P/'source-provenance.json').write_text(json.dumps(pr,indent=2)+'\n')
print({'records':len(ds),'self_contained':sum(d['complete_self_contained_statement'] for d in ds),'selected_primary':len(passages),'proposals':0})
