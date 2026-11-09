# Fresh extracted strict replay: unzip packet into empty dir, scan forbidden tokens, rebuild, audit axioms.
import zipfile, pathlib, hashlib, json, subprocess, re, shutil, datetime, sys
H=pathlib.Path(__file__).resolve().parent
pk=H/'proof-packet.zip'
files=['lean/Yip355956.lean','lean/V3Config355701.lean','lean/Audit.lean','lean/AuditV3.lean','lean/run_lean.py','lean/certificates.json','scripts/gen_yip_lean.py','scripts/gen_v3_lean.py','scripts/v3_template.lean']
if '--pack' in sys.argv:
    with zipfile.ZipFile(pk,'w',zipfile.ZIP_DEFLATED) as z:
        for f in files: z.write(H/f,f)
fresh=H/'fresh-extracted'
if fresh.exists(): shutil.rmtree(fresh)
fresh.mkdir()
with zipfile.ZipFile(pk) as z: z.extractall(fresh)
L=fresh/'lean'
forbidden=re.compile(r'\b(sorry|admit|axiom|unsafe|native_decide|ofReduceBool|implemented_by|extern|opaque|debug\.skipKernelTC)\b')
scan={}
for f in ['Yip355956.lean','V3Config355701.lean']:
    txt=(L/f).read_text(); scan[f]=[m.group(0) for m in forbidden.finditer(txt)]
log={}
def run(args,name):
    r=subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryMax=8G','-p','CPUQuota=200%','timeout','1700','python3','-I','run_lean.py',*args],cwd=L,capture_output=True,text=True)
    (H/'logs'/f'replay-{name}.log').write_text(r.stdout+r.stderr); log[name]=r.returncode; return r.stdout+r.stderr
run(['-o','Yip355956.olean','Yip355956.lean'],'build-yip')
run(['-o','V3Config355701.olean','V3Config355701.lean'],'build-v3')
a1=run(['Audit.lean'],'audit-yip'); a2=run(['AuditV3.lean'],'audit-v3')
allowed={'propext','Classical.choice','Quot.sound'}
def axsets(t):
    out=[]
    for line in t.splitlines():
        m=re.search(r"depends on axioms: \[(.*)\]",line)
        if m: out.append(set(x.strip() for x in m.group(1).split(',')))
    return out
bad=[s for s in axsets(a1)+axsets(a2) if not s<=allowed]
rec={'utc':datetime.datetime.now(datetime.UTC).isoformat(),'packet_sha256':hashlib.sha256(pk.read_bytes()).hexdigest(),
     'file_sha256':{f:hashlib.sha256((fresh/f).read_bytes()).hexdigest() for f in files},
     'forbidden_token_hits':scan,'returncodes':log,'axiom_lines':len(axsets(a1)+axsets(a2)),'disallowed_axiom_sets':[sorted(s) for s in bad],
     'audited_counts':re.findall(r'audited (\d+) declarations',a1+a2),
     'lean':'/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean (4.34.1, commit 5045d0056413266e57c625dcd7c365b10e377c52)',
     'mathlib':'d13f23b723b8a846827a245b89c10fc7d3f11612 prebuilt oleans (read-only, trusted, not rebuilt)',
     'flags':'-DwarningAsError=true -j2, LEAN_NUM_THREADS=2'}
rec['PASS']=all(v==0 for v in log.values()) and not bad and not any(scan.values())
(H/'replay-receipt.json').write_text(json.dumps(rec,indent=2)+'\n'); print(json.dumps(rec,indent=1))
