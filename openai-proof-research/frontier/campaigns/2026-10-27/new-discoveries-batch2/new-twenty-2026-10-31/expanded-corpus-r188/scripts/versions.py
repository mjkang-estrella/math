import pathlib,json,re,subprocess,sys
D=pathlib.Path(__file__).resolve().parents[1];out={};args=[]
for row in json.loads((D/'reservation.json').read_text())['rows']:
 i=str(row['mathdb_id']);s=(D/f'sources/{i}-abs.body').read_text();aid=row['source_url'].split('/')[-1]
 vs=sorted(set(re.findall(re.escape(aid)+r'v(\d+)',s)),key=int)
 doi=re.findall(r'name="citation_doi" content="([^"]+)',s)
 out[i]={'versions':vs,'doi':doi,'history':re.findall(r'\[v\d+\].{0,300}',s)}
 for v in vs:args += [i+'-v'+v,'https://arxiv.org/pdf/'+aid+'v'+v]
print(json.dumps(out,indent=2));(D/'outputs/version-inventory.json').write_text(json.dumps(out,indent=2))
subprocess.run([sys.executable,'-I',str(D/'scripts/fetch.py'),*args])
