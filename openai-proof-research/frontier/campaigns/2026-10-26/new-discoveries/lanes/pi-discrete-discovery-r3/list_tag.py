import json, subprocess, sys, time

def get(url):
    r = subprocess.run(["curl","-s","-A","Mozilla/5.0",url], capture_output=True, text=True)
    return json.loads(r.stdout)

tag = sys.argv[1]
seen = {}
offset = 0
while True:
    d = get(f"https://mathdb.com/api/posts?tag={tag}&limit=100&offset={offset}")
    items = d.get("items", [])
    if not items: break
    for it in items:
        seen[it["number"]] = it
    offset += 100
    if len(items) < 100: break
    time.sleep(0.3)
print(f"tag={tag} total={len(seen)}")
for n, it in sorted(seen.items()):
    sol = it.get("solution_count",0)
    st = it.get("status","")
    if st == "open" or (st not in ("solved","resolved","closed") and sol==0):
        print(f'{n}\t{st}\tsol={sol}\t{it.get("importance")}\t{it["title"][:80]}')
