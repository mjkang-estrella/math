from pathlib import Path
import re,json,hashlib
R=Path(__file__).parent
HEADERS=re.compile(r"^(?:[0-9]+\s+Pola.*Quittner and Souplet|Singularity (?:and decay |estimates via ).*[0-9]+|[0-9]+\s+QUOC HUNG PHAN|LIOUVILLE.*[0-9]+)$",re.I)
def show_primary(name,start,end):
 p=R/"private/primary"/(name+".txt");b=p.read_bytes();ls=b.splitlines(keepends=True);assert 1<=start<=end<=len(ls)
 offsets=[0]
 for line in ls:offsets.append(offsets[-1]+len(line))
 print(f"\nREAD {name}, parser bytes.splitlines, lines {start}-{end}, outer bytes [{offsets[start-1]},{offsets[end]})")
 omitted=[];shown=[]
 for i in range(start-1,end):
  line=ls[i];s=line.decode().strip().lstrip("\f").strip()
  if HEADERS.fullmatch(s):
   omitted.append([i+1,offsets[i],offsets[i+1],"running header"]);print(f"[MASK running header L{i+1}]")
  else:shown.append([offsets[i],offsets[i+1]]);print(line.decode(),end="")
 with (R/"private/read-extents.jsonl").open("a") as f:f.write(json.dumps({"path":str(p.relative_to(R)),"lines":[start,end],"outer_bytes":[offsets[start-1],offsets[end]],"omitted":omitted,"displayed_byte_ranges":shown,"full_text_sha256":hashlib.sha256(b).hexdigest()})+"\n")
