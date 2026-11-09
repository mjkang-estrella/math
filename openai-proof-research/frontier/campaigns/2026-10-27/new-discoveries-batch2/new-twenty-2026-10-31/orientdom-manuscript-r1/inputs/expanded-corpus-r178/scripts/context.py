import pathlib,json,re,hashlib,subprocess
D=pathlib.Path(__file__).resolve().parents[1];E=json.loads((D/'extracted.json').read_text());out={}
for i,r in E.items():
 row=r['row'];r['statement_sha256']=hashlib.sha256(row['statement'].encode()).hexdigest();a=row['source_url'].rsplit('/',1)[1];parts=[]
 for p in sorted((D/'sources').glob(a+'v*.pdf.txt')):
  lines=p.read_text().splitlines();matches=[n for n,s in enumerate(lines) if re.search(r'Conjecture|Corollary 1.3|Theorem 1.2|Theorem 1:',s)]
  for n in matches:parts.append('\nFILE '+p.name+' LINE '+str(n+1)+'\n'+'\n'.join(lines[max(0,n-4):n+15]))
 (D/f'outputs/{i}-source-context.txt').write_text('\n'.join(parts))
 # exact title search limited to campaign notes, not raw metadata
 p=subprocess.run(['rg','-l','-F',row['title'],str(D.parent.parent),'-g','SUMMARY.md','-g','results.json','-g','review.json'],capture_output=True,text=True)
 out[i]=p.stdout.splitlines()
(D/'extracted.json').write_text(json.dumps(E,indent=2)+'\n');(D/'outputs/history-titles.json').write_text(json.dumps(out,indent=2))
# render ledger facts to a readable compact listing
facts=[]
for p in (D/'outputs').glob('context-*.json'):
 j=json.loads(p.read_text());facts.append('\n'+p.name)
 for key in ['accepted','excluded','excluded_after_review','candidates','held_candidates','acceptance_gates','counting_standard']:
  if key in j:facts.append(key+': '+json.dumps(j[key],ensure_ascii=False))
(D/'outputs/family-context.txt').write_text('\n'.join(facts))
