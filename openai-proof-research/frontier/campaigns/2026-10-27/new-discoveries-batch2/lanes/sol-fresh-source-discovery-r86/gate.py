import pathlib,subprocess,json,re,gzip,hashlib
P=pathlib.Path(__file__).resolve().parent;R=P.parents[5]; B=P.parent
# Filename-first, all dates and all campaign/source reports, not lane-name priority.
cmd=['rg','-l','-i','Eruguz|103127|2603[.]18243|Hyman|2508[.]12915|box.fragmentation|Benford',str(R),'-g','*FINDINGS*','-g','*discovery*','-g','*SUMMARY*','-g','*provenance*','-g','*ledger*','-g','*context*','-g','*NEXT*','-g','!sol-fresh-source-discovery-r86/**']
a=subprocess.run(cmd,text=True,capture_output=True);names=[s for s in a.stdout.splitlines() if str(P) not in s];(P/'all-date-report-filenames.txt').write_text('\n'.join(names)+'\n')
rows=[]
for s in names:
 lines=pathlib.Path(s).read_text(errors='replace').splitlines();hits=[i for i,l in enumerate(lines) if re.search('Eruguz|103127|2603[.]18243|Hyman|2508[.]12915|box.fragmentation|Benford',l,re.I)]
 rows.append({'file':s,'sections':[{'line':i+1,'text':'\n'.join(lines[max(0,i-3):i+5])} for i in hits[:8]]})
# Actual nearest campaign exclusion bodies (methods rather than title evidence).
for rel in ['root-lasso-exclusion-r2/EXCLUSION.json','root-silicosis-exclusion-r1/EXCLUSION.json']:
 f=B/rel; rows.append({'file':str(f),'text':f.read_text()})
(P/'all-date-report-sections.json').write_text(json.dumps(rows,indent=2))
cache=B/'root-edge-irregulator-final-freeze-r1';reg=[]
for n in ['omega','openai']:
 f=cache/(n+'-tree.txt.gz');raw=gzip.decompress(f.read_bytes());lines=raw.decode().splitlines()
 reg.append({'repo':n,'file':str(f),'sha256_uncompressed':hashlib.sha256(raw).hexdigest(),'entries':len(lines),'specific_hits':[x for x in lines if re.search('Eruguz|103127|2603[.]18243|Hyman|2508[.]12915|Benford|CustomerToCustomer',x,re.I)]})
(P/'registry-cached-screen.json').write_text(json.dumps(reg,indent=2));print('report matches',len(names));print(json.dumps(reg,indent=2))
