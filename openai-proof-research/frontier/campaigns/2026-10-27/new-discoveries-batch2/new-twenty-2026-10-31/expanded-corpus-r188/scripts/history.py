import pathlib,json,subprocess
D=pathlib.Path(__file__).resolve().parents[1];ids=json.loads((D/'reservation.json').read_text())['ids']
pats='|'.join(str(i) for i in ids)
p=subprocess.run(['rg','-n','--glob','*.md','--glob','*results.json','--glob','*review.json',pats,str(D.parent.parent)],capture_output=True,text=True)
lines=[x for x in p.stdout.splitlines() if str(D)+'/' not in x and '/reservation.json' not in x and '/TASK.txt' not in x]
(D/'outputs/history-id-hits.txt').write_text('\n'.join(lines));print('\n'.join(lines)[:14000], '\nLINES',len(lines))
for p in (D/'outputs').glob('context*.json'):
 x=json.loads(p.read_text());print(p.name)
 for k in ('accepted','excluded','excluded_after_review','counting_standard','acceptance_gates'):
  if k in x:print(k,json.dumps(x[k],ensure_ascii=False)[:15000])
