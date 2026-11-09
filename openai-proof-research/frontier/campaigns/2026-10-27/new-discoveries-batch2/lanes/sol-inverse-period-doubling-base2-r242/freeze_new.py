exec((__import__('pathlib').Path(__file__).parent/'freeze.py').read_text().split('rows=[]')[0])
rows=json.loads((L/'bindings.json').read_text())
for p in (L/'new-sources').iterdir():
 d=L/'frozen/new-sources'/p.name;d.parent.mkdir(exist_ok=True);before=h(p);shutil.copyfile(p,d);assert h(p)==h(d)==before
 rows.append({'original':str(p),'copy':str(d.relative_to(L)),'sha256':before})
(L/'bindings.json').write_text(json.dumps(rows,indent=2))
