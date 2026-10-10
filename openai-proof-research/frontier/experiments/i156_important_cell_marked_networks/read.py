import sys,json,hashlib
from pathlib import Path
S=Path("frontier/sources/i156_important_cell_marked_networks")
p=Path(sys.argv[1]);a=int(sys.argv[2]);b=int(sys.argv[3]);raw=p.read_bytes();ls=raw.decode().splitlines();assert 1<=a<=b<=len(ls)
text="\n".join(ls[a-1:b]);print(f"{p} L{a}-{b}/{len(ls)}");print(text);print("END",repr(ls[b-1]))
r={"path":str(p),"start":a,"end":b,"total_lines":len(ls),"sha256":hashlib.sha256(raw).hexdigest(),"passage_sha256":hashlib.sha256(text.encode()).hexdigest(),"ending":ls[b-1],"displayed":True}
x=json.loads((S/"progress.json").read_text());x["read_passages"].append(r);(S/"progress.json").write_text(json.dumps(x,indent=2)+"\n")
