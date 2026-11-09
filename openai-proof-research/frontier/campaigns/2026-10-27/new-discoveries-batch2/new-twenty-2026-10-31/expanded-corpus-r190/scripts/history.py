import pathlib,subprocess,json
D=pathlib.Path(__file__).resolve().parents[1];R=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research');ids=json.loads((D/'reservation.json').read_text())['ids']
pat=r'\b(?:'+'|'.join(map(str,ids))+r')\b'
r=subprocess.run(['rg','-n','--max-columns','1000','--glob','*.md','--glob','results.json','--glob','!TASK.txt',pat,str(R)],capture_output=True,text=True)
lines=[s for s in r.stdout.splitlines() if str(D) not in s]
(D/'outputs/history-matches.txt').write_text('\n'.join(lines)+'\n');print('\n'.join(lines)[:6000]);print('matches',len(lines),'return',r.returncode)
