import json,pathlib
P=pathlib.Path(__file__).resolve().parent
rows=json.loads((P/'statements.json').read_text());notes={}
for line in (P/'technical-notes.tsv').read_text().splitlines():
 i,d,n=line.split('\t');notes[int(i)]=(d,n)
assert len(notes)==len(rows)==50
out=[]
primary={356681:'2210.17021v1; definitions47/49/50, conjecture53; v2 only overview inspected',356731:'2211.01495; derivative definitions/formula, theorem2.19 proof opening, conjecture2.20',357065:'2211.16637v2 pp2-3; LEsurvey11 p25 witness footnote',357226:'2301.05202v2 pp1-2 and section2.4 proof conclusion',357227:'2301.05202v2 pp1-2 Conjecture1.3',357229:'2301.05202v2 section3 Conjecture3.3 discussion',357318:'2301.09867v1 pp1-2 definitions and pp7-8 conjectures',357683:'2303.04892v4 section1 Conjecture1.6 and small-dimension discussion, section5 lower-bound conclusion'}
for r in rows:
 i=r['mathdb_id'];d,n=notes[i];out.append({k:r[k] for k in ['mathdb_id','corpus_path','line','statement','statement_sha256','canonical_record_sha256']}|{'title':r['record']['title'],'source_url_record':r['record']['source_url'],'disposition':d,'technical_assessment':n,'literal_statement_review':'complete, including quantifiers as literally present; omissions disclosed in assessment','primary_passage':primary.get(i,'not inspected'),'whole_primary_body_read':False,'full_dependency_audit':False,'local_calculation':'calculation-results.json' if i in [357065,357226,357683] else None,'registry':'HOLD: current proof registry unavailable; zero direct MathDB requests','novelty_cleared':False,'discovery_credit':0})
(P/'dispositions.json').write_text(json.dumps(out,ensure_ascii=False,indent=2)+'\n');(P/'proposals.json').write_text('[]\n')
print('50 individual dispositions; zero proposals')
