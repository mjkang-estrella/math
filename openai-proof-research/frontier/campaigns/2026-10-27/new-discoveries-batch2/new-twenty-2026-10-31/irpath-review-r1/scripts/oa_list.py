"""List OpenAlex works from a downloaded JSON body (data only). Usage: oa_list.py BODY [FILTER_SUBSTR]"""
import json, sys
d = json.load(open(sys.argv[1]))
flt = sys.argv[2].lower() if len(sys.argv) > 2 else ""
print("count", d.get("meta", {}).get("count"))
for w in d.get("results", []):
    t = w.get("title") or ""
    au = ", ".join(a["author"]["display_name"] for a in w.get("authorships", [])[:4])
    src = ((w.get("primary_location") or {}).get("source") or {}).get("display_name")
    line = "%s | %s | %s | %s | %s | %s | cited %s" % (w["id"].split("/")[-1], w.get("publication_year"), t, au, src, w.get("doi"), w.get("cited_by_count"))
    if flt in line.lower():
        print(line)
