import json,hashlib,os,subprocess,datetime
LANE="/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/pi-mathdb-primary-qualified-breadth-r327"
# mathdb_id -> list of (name,url)
F={
 "2407.19583":[("2407.19583v1.html","https://arxiv.org/html/2407.19583v1"),("2407.19583-abs.html","https://arxiv.org/abs/2407.19583")],
 "2406.01790":[("2406.01790v1.html","https://arxiv.org/html/2406.01790v1"),("2406.01790-abs.html","https://arxiv.org/abs/2406.01790")],
 "2504.21558":[("2504.21558-abs.html","https://arxiv.org/abs/2504.21558")],
 "2607.15501":[("2607.15501-abs.html","https://arxiv.org/abs/2607.15501")],
 "2312.07339":[("2312.07339-abs.html","https://arxiv.org/abs/2312.07339")],
 "2401.08271":[("2401.08271-abs.html","https://arxiv.org/abs/2401.08271")],
 "2403.12587":[("2403.12587-abs.html","https://arxiv.org/abs/2403.12587")],
 "2503.16839":[("2503.16839-abs.html","https://arxiv.org/abs/2503.16839")],
 "2504.03039":[("2504.03039-abs.html","https://arxiv.org/abs/2504.03039")],
 "2605.29166":[("2605.29166-abs.html","https://arxiv.org/abs/2605.29166")],
 "math.0111192":[("math-0111192-abs.html","https://arxiv.org/abs/math/0111192")],
 "math.0304180":[("math-0304180-abs.html","https://arxiv.org/abs/math/0304180")],
 "2511.14514":[("2511.14514-abs.html","https://arxiv.org/abs/2511.14514")],
 "2604.02404":[("2604.02404-abs.html","https://arxiv.org/abs/2604.02404")],
 "2605.05198":[("2605.05198-abs.html","https://arxiv.org/abs/2605.05198")],
 "1905.00832":[("1905.00832-abs.html","https://arxiv.org/abs/1905.00832")],
}
out=[]
for key,items in F.items():
    for name,url in items:
        dst=os.path.join(LANE,"sources",name)
        r=subprocess.run(["curl","-sS","--max-time","60","-L","-o",dst,"-w","%{http_code}",url],capture_output=True,text=True)
        code=r.stdout.strip()
        if code=="200" and os.path.exists(dst):
            h=hashlib.sha256(open(dst,'rb').read()).hexdigest()
            utc=datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
            out.append({"mathdb_key":key,"file":"sources/"+name,"url":url,"http":code,
                        "bytes":os.path.getsize(dst),"sha256":h,"utc":utc})
        else:
            out.append({"mathdb_key":key,"file":"sources/"+name,"url":url,"http":code,"error":r.stderr[:200]})
json.dump(out,open(LANE+"/work/source-bindings.json","w"),indent=1)
for o in out: print(o["file"],o.get("http"),o.get("bytes"),o.get("sha256","")[:12])
