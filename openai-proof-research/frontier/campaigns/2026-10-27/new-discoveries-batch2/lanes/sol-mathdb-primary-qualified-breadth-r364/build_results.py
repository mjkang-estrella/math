from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).parent;L=R.parent
rows=[json.loads(x[7:]) for x in (R/'reading.log').read_text().splitlines() if x.startswith('RECORD ')]
notes={int(a):(b,c) for a,b,c in [x.split('\t',2) for x in (R/'disposition-notes.tsv').read_text().splitlines()]}
refs={int(x['id']):x for x in json.loads((R/'record-refs.json').read_text())}
assert len(rows)==len(notes)==50
out=[]
primary={320288:'Section5 Theorem4 proof and Corollary3',325538:'Conjecture2.48, Remarks2.47–2.49 and source examples',337039:'Conjecture1, Lemma5 proof, Corollary1, Section6 Conclusion',340760:'Theorems18–19 proofs and Conjecture20',341533:'Theorem39 proof, Examples37/40 and final Conjecture42'}
for r in rows:
 n=r['mathdb_id'];d,reason=notes[n]
 out.append({'mathdb_id':n,'title':r['title'],'literal_statement':r['statement'],'source_url':r['source_url'],'record_ref':refs[n],'disposition':d,'reason':reason,'evidence_level':'primary_statement_and_local_proof_sections' if n in primary else 'literal_record_statement_only','primary_sections_read':primary.get(n),'record_review':True,'primary_statement_review':n in primary,'concluding_proof_section_review':n in {320288,337039,340760,341533},'complete_proof_dependency_coverage':n==337039,'complete_proof_coverage_scope':'independent ordinary derivation only; not the full source paper' if n==337039 else None,'bounded_novelty':'not cleared; no promotion','credit':0})
(R/'dispositions.json').write_text(json.dumps(out,indent=2,ensure_ascii=False)+'\n');(R/'proposals.json').write_text('[]\n')
# Keep the record-reading evidence capped and avoid an extra copy of full records beyond the fifty dispositions.
(R/'reading.log').write_text('\n'.join(x for x in (R/'reading.log').read_text().splitlines() if not x.startswith('RECORD '))+'\n')
(R/'show.py').unlink()
print('50 dispositions; zero proposals; ordinary proof retained')
