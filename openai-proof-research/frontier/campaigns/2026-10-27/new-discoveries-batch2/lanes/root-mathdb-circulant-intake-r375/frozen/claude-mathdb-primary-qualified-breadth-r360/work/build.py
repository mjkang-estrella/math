from pathlib import Path
import json
L=Path(__file__).resolve().parents[1]
recs=json.loads((L/'records.json').read_text()); J=json.loads((L/'work/judgments.json').read_text())
body={367396,367397,368940,372627,372628}
out=[]
for d in recs:
    i=d['mathdb_id']; disp,reason,ev=J[str(i)]
    out.append({'mathdb_id':i,'title':d['title'],'literal_statement_sha256':d['literal_statement_sha256'],
      'source_url':d['source_url'],'corpus_path':d['corpus_path'],'corpus_line':d['corpus_line'],
      'disposition':disp,'reason':reason,'evidence_level':ev,'record_statement_review':True,
      'primary_body_review':i in body,'resolution_proof_body_section_read':False,'full_resolution_proof_body_read':False,
      'proof_body_applicability':{368940:'complete ordinary proof here (briefs/368940.md); independent review pending',
                                  372627:'complete computer-certificate proof here (lower and upper bound); review pending',
                                  372628:'lower-bound certificate here; upper bound from source Theorem 24 (read statement and proof sketch)',
                                  367397:'successor Theorem 1 statement matches exactly; successor proof not audited; independent replay in replays/'}.get(i,'none'),
      'mathematical_evidence':{368940:'ordinary proof plus exact identity check',372627:'finite certificate plus brute-force cross-check',372628:'finite certificate plus brute-force cross-check (odd n<=45, n=105)',367397:'ordinary proof plus check g<=120'}.get(i,'none'),
      'novelty_review':'not cleared','prior_cleared':False,'source_scope_cleared':False,'accepted_credit':0})
assert len(out)==50 and len({x['mathdb_id'] for x in out})==50
(L/'dispositions.json').write_text(json.dumps({'dispositions':out},indent=1,ensure_ascii=False)+'\n')
from collections import Counter; print(Counter(x['disposition'] for x in out))
