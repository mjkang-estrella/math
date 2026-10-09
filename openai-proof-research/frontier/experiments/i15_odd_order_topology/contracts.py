#!/usr/bin/env python3
"""Extract exact source statements; this does not audit their truth."""
import json,re,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
OUT=ROOT/"frontier/sources/i15_odd_order_topology"
UP=OUT/"upstream"
names=["Nonhomeomorphic-closed-aspherical-four-manifolds-with-the-same-homotopy-type-October-4-2026",
"A-marked-tensor-obstruction-to-four-dimensional-disk-embedding-September-24-2026",
"A-PD4-group-without-an-aspherical-manifold-model-September-24-2026",
"A-boundary-only-obstruction-to-four-dimensional-disk-embedding-September-24-2026"]
out=[]
pat=re.compile(r"\\begin\{(theorem|proposition|lemma|corollary|remark)\}(.*?)\\end\{\1\}",re.S)
for name in names:
 for p in sorted((UP/"preprints"/name).rglob("*.tex")):
  b=p.read_bytes(); s=b.decode()
  for m in pat.finditer(s):
   labels=re.findall(r"\\label\{([^}]+)\}",m.group())
   out.append(dict(path=str(p.relative_to(UP)),url="https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/"+str(p.relative_to(UP)),
    labels=labels,start_line=s[:m.start()].count("\n")+1,end_line=s[:m.end()].count("\n")+1,
    source_sha256=hashlib.sha256(b).hexdigest(),statement=m.group(),statement_sha256=hashlib.sha256(m.group().encode()).hexdigest()))
(OUT/"contracts.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(dict(statements=len(out),manuscripts=len(names))))

