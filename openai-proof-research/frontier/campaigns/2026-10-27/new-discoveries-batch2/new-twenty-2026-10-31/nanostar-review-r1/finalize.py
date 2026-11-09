import pathlib,json,hashlib,datetime,re
p=pathlib.Path.cwd()
before=json.loads((p/'inputs-before.json').read_text())
after={k:hashlib.sha256(pathlib.Path(k).read_bytes()).hexdigest() for k in before}
(p/'inputs-after.json').write_text(json.dumps(after,indent=2))
assert before==after, 'READ-ONLY INPUT CHANGED'
receipts=[]
for d in sorted((p/'downloads').iterdir()):
 if not d.is_dir():continue
 receipts.append({'directory':str(d.relative_to(p)),'url':(d/'url').read_text().strip(),'status':(d/'status').read_text().strip(),'sha256':hashlib.sha256((d/'body').read_bytes()).hexdigest() if (d/'body').exists() else None,'error':(d/'error').read_text()})
(p/'network-receipts.json').write_text(json.dumps({'review_date':'2026-11-04','receipts':receipts},indent=2))
inv=(p/'logs/inventory.log').read_text()
audit=(p/'logs/audit.log').read_text()
names=set(re.findall(r'^R162\.[^\s]+',inv,re.M))
audited=set(re.findall(r"^'([^']+)'",audit,re.M))
assert names<=audited,(names-audited)
assert not re.search(r'\bsorryAx\b',audit)
sets=re.findall(r'depends on axioms: \[([^\]]*)\]',audit)
axioms=sorted({a.strip() for s in sets for a in s.split(',') if a.strip()})
assert set(axioms)<={'propext','Classical.choice','Quot.sound'},axioms
summary={'inputs':len(before),'unchanged':before==after,'local_names':len(names),'audited_names':len(audited),'axioms':axioms,'proof_zip_sha256':before[str(p.parent/'expanded-corpus-r162/proof-source.zip')]}
(p/'validation-summary.json').write_text(json.dumps(summary,indent=2))
print(json.dumps(summary,indent=2))
