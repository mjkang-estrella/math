import pathlib,json,re,subprocess,hashlib
p=pathlib.Path(__file__).resolve().parent;data=json.loads((p/'extracted.json').read_text());hist={}
for i,x in data.items():
 r=x['record'];terms=[r['title'],r['source_url'].rsplit('/',1)[-1]];pattern=r'\b'+i+r'\b|'+ '|'.join(re.escape(t) for t in terms)
 proc=subprocess.run(['rg','-n','-i','--glob','*.md','--glob','*.json','--glob','*.txt','--glob','!mathdb*','--glob','!reservation.json',pattern,str(p.parents[3])],capture_output=True,text=True,timeout=15)
 lines=[line for line in proc.stdout.splitlines() if str(p) not in line and len(line)<1800];hist[i]={'terms':terms,'matches':lines[:60],'truncated':len(lines)>60}
(p/'history-matches.json').write_text(json.dumps(hist,indent=2));print(json.dumps({i:v['matches'] for i,v in hist.items() if v['matches']},indent=2)[:15000])
