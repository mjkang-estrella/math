import pathlib,zipfile,hashlib,re,json,difflib
root=pathlib.Path.cwd(); src=root/'source'
z=zipfile.ZipFile(root.parent/'delta-formal-r2/source.zip')
changes=[];unchanged=[]
for name in z.namelist():
 p=src/name
 if not p.is_file(): continue
 a=z.read(name);b=p.read_bytes()
 sha=lambda x:hashlib.sha256(x).hexdigest()
 if a==b:unchanged.append(name);continue
 if name.startswith('lean/'):
  # Removing only the newly added helper theorems and reverting the census proof
  # must reproduce the original byte for byte.
  text=b.decode()
  if name in ("lean/Literal.lean", "lean/Delta153.lean"):
   text=text.replace("import Mathlib.Data.Fintype.BigOperators\nimport Mathlib.Data.List.FinRange\nimport Mathlib.Tactic.NormNum\nimport Mathlib.Tactic.IntervalCases", "import Mathlib.Tactic")
  text=re.sub(r'theorem census_node\d+[^\n]*\n','',text)
  text=re.sub(r'(theorem arc_count\d+[^\n]*:= )by\n  simp only [^\n]*\n  decide \+kernel',r'\1by decide +kernel',text)
  assert text.encode()==a, name
 changes.append(dict(file=name,before_sha256=sha(a),after_sha256=sha(b),data_and_original_statements_unchanged=True if name.startswith('lean/') else None))
 (root/'logs'/'changes.diff').open('a').write(''.join(difflib.unified_diff(a.decode().splitlines(True),b.decode().splitlines(True),fromfile='round2/'+name,tofile='round3/'+name)))
(root/'changes.json').write_text(json.dumps(dict(changes=changes,byte_identical=unchanged),indent=2)+'\n')
print(len(changes),'changed;',len(unchanged),'byte-identical; all Lean changes verified proof-only')
final=zipfile.ZipFile(root/'source.zip')
added=[dict(file=n,sha256=hashlib.sha256(final.read(n)).hexdigest()) for n in final.namelist() if not n.endswith('/') and n not in z.namelist()]
report=json.loads((root/'changes.json').read_text());report['added']=added
for n in final.namelist():
 if not n.endswith('/'):
  assert final.read(n)==(src/n).read_bytes(),n
report['final_archive_matches_source']=True
(root/'changes.json').write_text(json.dumps(report,indent=2)+'\n')
print('Added files:',added)
