"""Read-only exact-selection verifier. Anchors must be supplied explicitly."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, stat

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def check_file(p, row):
    st=p.lstat()
    if not stat.S_ISREG(st.st_mode):
        raise ValueError("not a regular file: "+str(p))
    if stat.S_IMODE(st.st_mode)!=int(row["mode"],8):
        raise ValueError("mode mismatch: "+str(p))
    if st.st_size!=row["bytes"] or digest(p)!=row["sha256"]:
        raise ValueError("byte mismatch: "+str(p))

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--final-sha256",required=True)
    ap.add_argument("--manifest-sha256",required=True)
    ap.add_argument("--report-sha256",required=True)
    ap.add_argument("--copied-controls",action="store_true")
    a=ap.parse_args(); root=Path(__file__).resolve().parent
    supplied={"FINAL.md":a.final_sha256,"MANIFEST.json":a.manifest_sha256,"REPORT.md":a.report_sha256}
    for name,h in supplied.items():
        if len(h)!=64 or any(c not in "0123456789abcdef" for c in h):
            raise ValueError("invalid explicit anchor")
        if digest(root/name)!=h:
            raise ValueError("detached anchor mismatch: "+name)
        if stat.S_IMODE((root/name).stat().st_mode)!=0o444:
            raise ValueError("detached mode mismatch: "+name)
    manifest=json.loads((root/"MANIFEST.json").read_text())
    rows=manifest["files"]; paths=[x["path"] for x in rows]
    if paths!=sorted(set(paths)):
        raise ValueError("noncanonical or duplicate selection")
    outside=set(manifest["outside_selection"])
    for s in paths+sorted(outside):
        p=PurePosixPath(s)
        if p.is_absolute() or ".." in p.parts or str(p)!=s:
            raise ValueError("invalid packet path")
    actual=set()
    for p in root.rglob("*"):
        if p.is_symlink():
            raise ValueError("symlink in packet")
        if p.is_file():actual.add(p.relative_to(root).as_posix())
    if actual-outside!=set(paths):
        raise ValueError("exact-selection mismatch")
    for row in rows:check_file(root/row["path"],row)
    result={"artifact_verification":"selected bytes, sizes, modes and explicit anchors match", "selected_files":len(rows),"anchors":supplied,"mathematical_gate":False}
    if a.copied_controls:
        original=next(row for row in rows if row["path"]=="FINAL.md")
        check_file(root/"controls/FINAL.copy",original)
        rejected=[]
        for name in ["FINAL.changed","FINAL.mode"]:
            try:check_file(root/"controls"/name,original)
            except ValueError as exc:rejected.append({"copy":name,"rejection":str(exc).split(":")[0]})
            else:raise ValueError("copied control unexpectedly accepted")
        if digest(root/"FINAL.md")!=a.final_sha256:
            raise ValueError("original changed during controls")
        result["copied_controls"]={"unaltered_copy":"matches","expected_rejections":rejected,"original":"unchanged"}
    print(json.dumps(result,indent=2))

if __name__=="__main__":main()
