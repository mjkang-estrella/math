import sys,json
from pathlib import Path
S=Path("frontier/sources/i156_important_cell_marked_networks");p=Path("frontier/sources/i151_spatial_dynamical_percolation_continuation/context-reading-plan.json");d=json.loads(p.read_text());i=int(sys.argv[1]);cache={};x=json.loads((S/"progress.json").read_text());seen=set()
for r in x["read_passages"]:
 seen.update(Path(r["path"]).read_text().splitlines()[r["start"]-1:r["end"]])
indices=json.loads((S/"context-unread-indices.json").read_text())
selected=indices[i*100:(i+1)*100] if len(sys.argv)>2 else d["chunks"][i]
for j in selected:
 g=d["groups"][j];r=g["representative"];path=r["path"];cache.setdefault(path,Path(path).read_text().splitlines());line=cache[path][r["line"]-1]
 if line in seen:continue
 print(f"[{j} {Path(path).name}:{r['line']}; x{len(g['occurrences'])}]");print(line)
print("END CHUNK",i)
x.setdefault("context_extra_read",[]).extend(selected) if len(sys.argv)>2 else x["context_chunks_read"].append(i);(S/"progress.json").write_text(json.dumps(x,indent=2)+"\n")
