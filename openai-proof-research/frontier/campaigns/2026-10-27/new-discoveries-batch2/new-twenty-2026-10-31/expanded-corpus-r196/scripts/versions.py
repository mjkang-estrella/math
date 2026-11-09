import pathlib,json,re,sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from fetch import fetch,D
p=D/'outputs/denied-hosts.json';den=json.loads(p.read_text()) if p.exists() else [];p.write_text(json.dumps(sorted(set(den+['www.sciencedirect.com','sciencedirect.com','api.crossref.org']))))
out={}
for row in json.loads((D/'reservation.json').read_text())['rows']:
 i=str(row['mathdb_id']);b=next((D/'sources').glob(i+'-abs-*/body')).read_text();vers=sorted(set(re.findall(r'/abs/[^"<> ]+(v\d+)',b)));dois=re.findall(r'<meta name="citation_doi" content="([^"]+)"',b)
 out[i]={'versions_listed':vers,'downloaded_versions':[x.name for x in (D/'sources').glob(i+'-v*-pdf-*')],'dois':dois,'version_of_record_receipts':[]}
 for doi in dois:out[i]['version_of_record_receipts'].append(fetch('https://doi.org/'+doi,i+'-vor'))
(D/'outputs/versions.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
