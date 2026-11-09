import json, subprocess, sys

def get(num):
    r = subprocess.run(["curl","-s","-A","Mozilla/5.0",f"https://mathdb.com/api/posts/{num}"], capture_output=True, text=True)
    return json.loads(r.stdout)

for num in sys.argv[1:]:
    d = get(num)
    json.dump(d, open(f"sources/m{num}.json","w"), indent=1)
    print("="*90)
    print("NUM", d.get("number"), "|", d.get("title"))
    print("type:", d.get("post_type"), "status:", d.get("status"), "tags:", d.get("tags"))
    print("solutions:", len(d.get("solutions",[])), "comments:", len(d.get("comments",[])), "attachments:", len(d.get("attachments",[])))
    body = d.get("body") or d.get("content") or ""
    print("BODY len", len(body))
    print(body[:3500])
    for s in d.get("solutions", []):
        print("--- SOLUTION", s.get("id","")[:8], s.get("author","?"), s.get("status"))
        sb = s.get("body","")
        print(sb[:800])
    for c in d.get("comments", []):
        print("--- COMMENT", c.get("author","?"), c.get("body","")[:400])
