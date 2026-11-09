import pathlib,hashlib,json,sys,resource
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
b=pathlib.Path(__file__).resolve().parent.parent
files=[]
r=b/'nut-formal-r7q'
for n in ['SUMMARY.md','GAPS.md','statement-correspondence.md','source-fixes.json','development-validation.json','audit.log','audit-log-index.json','negative-controls.json','negative-controls-receipts.json','closure.json','nut-r7q-source.zip']:
 files.append(r/n)
files+=list((r/'formal').rglob('*'))
for lane in ['r1','r2','r3a','r3b','r4a','r4b','r5p','r5q','r6p','r6q']:
 files += [b/('nut-formal-'+lane)/n for n in ['SUMMARY.md','GAPS.md','root-integration.json']]
files += [b/'nut-interface-r5/NutInterface.lean',b/'nut-formal-r1/PRIOR-ART.md',b/'expanded-corpus-r111/NUT-ROUTE.md']
files+=list((b/'expanded-corpus-r111/sources').glob('365943.*'))
files+=list((b/'expanded-corpus-r111').rglob('nuts-resolver.py'))
files+=list((b/'nut-parent-final-r1').rglob('*'))
d={str(p.relative_to(b)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(files)) if p.is_file()}
(b/'nut-review-r1'/sys.argv[1]).write_text(json.dumps(d,indent=2)+'\n')
print(len(d),'files',d['nut-formal-r7q/nut-r7q-source.zip'])
