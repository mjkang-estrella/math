import pathlib,json,subprocess,hashlib
D=pathlib.Path(__file__).resolve().parents[1]; rows=json.loads((D/'reservation.json').read_text())['rows'];pat=r'\b(?:'+'|'.join(str(r['mathdb_id']) for r in rows)+r')\b'
p=subprocess.run(['rg','-n','--glob','SUMMARY.md','--glob','results.json','--glob','*review.json',pat,str(D.parent.parent)],text=True,capture_output=True)
lines=[s for s in p.stdout.splitlines() if str(D)+'/' not in s]
(D/'outputs/history-exact-id-hits.txt').write_text('\n'.join(lines));print('exact id history hits',len(lines));print('\n'.join(lines)[:3000])
pat='binary diagonal|signed.shift|cordial.*hypertree|subcritical.*covariance|five.element poset|partitioned.Kneser|Spiga|Ban.Linial'
p=subprocess.run(['rg','-n','-i','--glob','SUMMARY.md',pat,str(D.parent.parent)],text=True,capture_output=True)
lines=[s for s in p.stdout.splitlines() if str(D)+'/' not in s];(D/'outputs/history-title-hits.txt').write_text('\n'.join(lines));print('title history',len(lines));print('\n'.join(lines)[:5000])
