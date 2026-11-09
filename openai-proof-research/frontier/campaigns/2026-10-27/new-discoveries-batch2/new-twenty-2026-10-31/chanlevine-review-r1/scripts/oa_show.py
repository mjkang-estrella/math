"""Print a compact summary of an OpenAlex JSON response (untrusted data; parsed only)."""
import json, sys
d = json.load(open(sys.argv[1]))
res = d.get("results", [d]) if isinstance(d, dict) else d
if isinstance(d, dict) and "meta" in d:
    print("meta", d["meta"])
for w in res:
    ids = w.get("ids", {})
    au = ", ".join(a.get("author", {}).get("display_name", "?") for a in w.get("authorships", [])[:6])
    print("|", w.get("id"), "|", w.get("publication_year"), "|", (w.get("display_name") or "")[:110], "|", au[:80], "| doi", w.get("doi"), "| cited_by", w.get("cited_by_count"))
