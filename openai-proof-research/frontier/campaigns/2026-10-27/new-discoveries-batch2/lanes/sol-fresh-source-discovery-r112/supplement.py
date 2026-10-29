from pathlib import Path
p=Path(__file__).with_name('audit2.py')
s=p.read_text()
s=s.replace("if not wanted:continue", "if p.suffix.lower() not in ['.md','.py','.sh'] and not (any(x in lo for x in ['tools/','scripts/','agent/','openproblem']) and p.suffix.lower() in ['.txt','.json','.yaml','.yml']):continue")
s=s.replace('required-content','supplement-content').replace('required-hashes','supplement-hashes').replace('required-hits','supplement-hits')
exec(compile(s,str(p),'exec'))
