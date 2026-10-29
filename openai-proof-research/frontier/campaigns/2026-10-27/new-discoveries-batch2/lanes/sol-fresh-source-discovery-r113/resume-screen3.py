from pathlib import Path
import json
L=Path(__file__).parent
last=None
with (L/'screen-hashes-part2.jsonl').open() as f:
 for line in f:
  try:last=json.loads(line)['path']
  except (ValueError,KeyError):pass
assert last
code=(L/'screen.py').read_text()
code=code.replace("n=hits=errors=omitted=0", "n=hits=errors=omitted=0\nresume_after="+repr(last)+"\nresuming=True")
code=code.replace("p=Path(base,name);rel=str(p.relative_to(R))", "p=Path(base,name);rel=str(p.relative_to(R))\n   if resuming:\n    if rel==resume_after:resuming=False\n    continue")
for stem in ['screen-content','screen-hashes','screen-hits']:code=code.replace(stem+'.jsonl',stem+'-part3.jsonl')
print(json.dumps({'resume_after':last}),flush=True)
exec(compile(code,str(L/'screen.py'),'exec'))
