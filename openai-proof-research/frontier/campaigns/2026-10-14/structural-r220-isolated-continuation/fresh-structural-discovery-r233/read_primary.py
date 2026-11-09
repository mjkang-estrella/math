from pathlib import Path
import sys,json,hashlib,re
R=Path("frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r233")
k,a,z=sys.argv[1],int(sys.argv[2]),int(sys.argv[3]);p=R/"private-primary"/k/"article.tex";b=p.read_bytes();lines=b.splitlines(keepends=True);off=[0]
for l in lines:off.append(off[-1]+len(l))
enc=next(o["tex_encoding"] for o in json.loads((R/"primary-access.json").read_text()) if o["id"]==k)
assert 1<=a<=z<=len(lines)
print(f"PRIMARY READ {k} lines {a}-{z} bytes [{off[a-1]},{off[z]})")
masked=[]
for i in range(a-1,z):
 s=lines[i].decode(enc).rstrip()
 if s.lstrip().startswith("%"):
  masked.append({"line":i+1,"reason":"TeX comment"});continue
 if re.search(r"acknow|aknow|we (?:would like to )?thank|authors? (?:would like|wish|thank)|private.{0,12}communicat|personal.{0,12}communicat|copyright|funded by|\\thanks",s,re.I):
  masked.append({"line":i+1,"reason":"editorial candidate; mathematical ambiguity must be recovered"});print(str(i+1)+": [EDITORIAL CANDIDATE MASKED]");continue
 print(str(i+1)+": "+s)
with (R/"semantic-reads.jsonl").open("a") as f:f.write(json.dumps({"file":str(p.relative_to(R)),"lines":[a,z],"bytes":[off[a-1],off[z]],"sha256":hashlib.sha256(b).hexdigest(),"masked":masked,"parser":"bytes.splitlines(keepends=True)","selection":"mathematical section/result boundaries classified before display"})+"\n")
