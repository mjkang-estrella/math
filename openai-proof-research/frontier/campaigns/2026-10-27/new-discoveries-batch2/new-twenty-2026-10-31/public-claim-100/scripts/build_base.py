#!/usr/bin/env python3
"""Build base-rows.json: one row per accepted result from ledger + acceptance files + corpus + SUBMISSION.md."""
import json,os,re,sys,glob
C=os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0,os.path.join(C,'root-intake-r60'))
from corpus_row import row as corpus
L=json.load(open(os.path.join(C,'ledger.json')))
subs={int(d.split('-')[0]):d for d in os.listdir(os.path.join(C,'mathdb-submissions')) if d[0].isdigit()}
def load(a):
    if 'file' in a:
        for p in (a['file'],'root-intake-r60/'+a['file']):
            p=os.path.join(C,p)
            if os.path.exists(p): return json.load(open(p)),os.path.relpath(p,C)
    if 'acceptance' in a:
        v=a['acceptance']
        if isinstance(v,str): return json.load(open(os.path.join(C,v))),v
        return v,'ledger.json#accepted'
    return a,'ledger.json#accepted'
rows=[]
for n,a in enumerate(L['accepted'],1):
    i=int(a['mathdb_id']); d,accfile=load(a)
    cr=corpus(i) or {}
    sub=subs.get(i); subm=open(os.path.join(C,'mathdb-submissions',sub,'SUBMISSION.md')).read() if sub else ''
    m=re.search(r'Outcome:\s*\*\*([A-Z ]+)\*\*',subm)
    outcome=d.get('outcome') or (m.group(1) if m else None)
    st=str(d.get('status',''))
    if not outcome: outcome='REFUTED' if 'REFUT' in st.upper() else ('PROVED' if 'PROV' in st.upper() else None)
    ep=d.get('endpoints') or d.get('exact_endpoint') or d.get('endpoint')
    lanes=d.get('lanes') or {}
    replay=(d.get('final_replay') or lanes.get('final_replay') or lanes.get('final_replay_and_paper_check') or d.get('independent_extracted_replay_lane')
            or d.get('replay_receipts') or d.get('independent_replay_receipts') or d.get('independent_execution_receipts') or (d.get('formal') or {}).get('report') or (d.get('independent_review') if i==344485 else None) or d.get('validation'))
    ax=d.get('axioms') or (d.get('validation') or {}).get('allowed_axioms') or (d.get('formal') or {}).get('axioms')
    if i==344485 and not ax: ax=['propext','Classical.choice','Quot.sound']  # rhombic-full-final-independent-strict-replay-sol-r1/REPLAY-AND-FIDELITY-v1.md line 43
    rows.append({'n':n,'mathdb_id':i,'title':d.get('title') or cr.get('title'),'record_title':cr.get('title'),
      'statement':cr.get('statement'),'source':cr.get('source_name'),'source_url':cr.get('source_url'),
      'outcome':outcome,'status':st,'endpoints':ep,'axioms':ax,'replay':replay,'paper':d.get('paper'),
      'accepted_utc':d.get('accepted_utc') or d.get('utc') or a.get('accepted_utc') or a.get('utc'),
      'scope':d.get('scope') or (d.get('significance') or {}).get('root_decision'),
      'limits':d.get('remaining_literature_limits') or (d.get('significance') or {}).get('caveat'),
      'acceptance_file':accfile,'submission':('mathdb-submissions/'+sub) if sub else None})
json.dump(rows,open(os.path.join(C,'public-claim-100','base-rows.json'),'w'),indent=1,ensure_ascii=False)
for k in ['statement','outcome','endpoints','axioms','replay','paper','accepted_utc','submission','source_url']:
    print(k,'missing:',[r['mathdb_id'] for r in rows if not r[k]])
from collections import Counter
print(Counter(r['outcome'] for r in rows)); print(Counter(json.dumps(r['axioms']) for r in rows))
