from pathlib import Path
import hashlib,json,shutil
r=Path(__file__).resolve().parent;p=r.parent
h=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
files=[]
for name in ['edgepattern-formal-r5/formal','edgepattern-formal-r5/scripts','edgepattern-formal-r5/checks','edgepattern-formal-r5/negative-controls','edgepattern-formal-r1/prior','edgepattern-review-r1']:
 files += [x for x in (p/name).rglob('*') if x.is_file() and not x.suffix in ['.olean','.ilean','.pyc'] and '/fresh/' not in str(x)]
for name in ['edgepattern-formal-r5/edgepattern-r5-source.zip','edgepattern-formal-r5/auditor-final-source.zip','edgepattern-formal-r5/SUMMARY.md','edgepattern-formal-r5/statement-correspondence.md','edgepattern-formal-r5/REPRODUCE.md','edgepattern-formal-r5/closure.json','edgepattern-formal-r1/PRIOR-ART.md','edgepattern-formal-r1/PRIOR-ART.json','edgepattern-formal-r1/statement-correspondence.md','expanded-corpus-r103/EDGE-PROOF.md','expanded-corpus-r103/raw/342414.jsonl','edgepattern-root-adjudication-r1.json']:
 files.append(p/name)
files += list((p/'edgepattern-formal-r5').glob('*receipt.json'))
files += list((p/'expanded-corpus-r103/sources').glob('1904.05618*'))
files=sorted(set(files)); before={str(x.relative_to(p)):h(x) for x in files}
(r/'input-hashes-before.json').write_text(json.dumps(before,indent=2)+'\n')
for d in ['sources','evidence','receipts','paper','qa','scripts']:(r/d).mkdir(exist_ok=True)
for x in files:
 rel=x.relative_to(p)
 if rel.parts[0]=='edgepattern-formal-r5' and rel.parts[1] in ['formal','scripts','checks','negative-controls']:
  target=r/Path(*rel.parts[1:])
 else:target=r/'evidence'/rel
 target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(x,target)
(r/'INPUT-COPY-MANIFEST.json').write_text(json.dumps({str((r/('formal/'+x.name)).relative_to(r)) if x.parent.name=='formal' and x.parent.parent.name=='edgepattern-formal-r5' else str(x.relative_to(p)):h(x) for x in files},indent=2)+'\n')
print(len(files),'bound inputs; copied',len(list((r/'formal').glob('*.lean'))),'Lean files')
