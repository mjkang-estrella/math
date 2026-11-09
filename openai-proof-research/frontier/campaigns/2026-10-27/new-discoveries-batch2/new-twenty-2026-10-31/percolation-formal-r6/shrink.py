import pathlib,json,collections
r=pathlib.Path(__file__).resolve().parent;d=json.loads((r/'normalized-trimmed.json').read_text());seen={};duplicates=0;counts=collections.Counter()
for i,c,h in d['steps']:
 key=tuple(sorted(set(c)))
 if key in seen:duplicates+=1
 else:seen[key]=i
 counts[len(h)]+=1
out={'steps':len(d['steps']),'duplicate_derived_literal_sets':duplicates,'distinct_derived_literal_sets':len(seen),'hint_uses':sum(len(h) for _,_,h in d['steps']),'status':'external structural analysis only; no altered certificate proved','interpretation':'Literal-set deduplication is a possible compression, but needs replacement hints and a newly checked dependency graph. No symmetry constraint was added.'}
(r/'certificate-shrink-analysis.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
