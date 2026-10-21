"""Read-only artifact verifier; no mathematical or acceptance judgment."""
from pathlib import Path
import argparse, hashlib, json

def sha(b):
    return hashlib.sha256(b).hexdigest()

def check_payload(root, entries):
    expected=set()
    for e in entries:
        name=e["path"]; rel=Path(name)
        assert not rel.is_absolute() and ".." not in rel.parts
        p=root/rel
        assert not p.is_symlink() and p.resolve().is_relative_to(root)
        b=p.read_bytes()
        assert len(b)==e["bytes"] and sha(b)==e["sha256"], name
        assert name not in expected
        expected.add(name)
    excluded={"MANIFEST.json","REPORT.md","ANCHORS.json"}
    actual={p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()}
    assert actual-excluded==expected, (actual-excluded-expected,expected-actual)
    return len(expected)

def check_sources(root):
    auth=json.loads((root/"private/source-auth.json").read_text())
    prefix="frontier/campaigns/2026-10-14/fresh-analytic-discovery-r172/"
    for e in auth:
        assert e["local"].startswith(prefix)
        b=(root/e["local"][len(prefix):]).read_bytes()
        assert len(b)==e["bytes"] and sha(b)==e["sha256"]
        assert hashlib.sha1(b"blob "+str(len(b)).encode()+b"\0"+b).hexdigest()==e["git_blob"]
    return len(auth)

def check_originals(root, project):
    anchors=json.loads((root/"private/direct-anchors.json").read_text())
    for e in anchors:
        p=project/e["path"]
        with p.open("rb") as f:
            f.seek(e["start"]);b=f.read(e["end"]-e["start"])
        assert len(b)==e["end"]-e["start"] and sha(b)==e["sha256"], e["path"]
    selected=json.loads((root/"private/original-extents.json").read_text())
    for e in selected:
        # Whole-file digest was recorded during eligible navigation; it is not a semantic read.
        b=(project/e["path"]).read_bytes()
        assert len(b)==e["bytes"] and sha(b)==e["sha256"]
        assert sha(b[e["start"]:e["end"]])==e["selected_sha256"]
    return len(anchors),len(selected)

def check_controls(root):
    p=root/"private/controls"; e=json.loads((p/"expected.json").read_text())
    assert sha((p/"same.bin").read_bytes())==e["sha256"]
    assert sha((p/"changed.bin").read_bytes())!=e["sha256"]
    return "copied positive accepted; copied one-byte change rejected"

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ("final-sha256","manifest-sha256","report-sha256","project-root"):
        parser.add_argument("--"+name,required=True)
    a=parser.parse_args();root=Path(__file__).resolve().parent
    project=Path(a.project_root).resolve()
    assert project==Path("/home/mj-kang/Documents/Dev/math/openai-proof-research")
    for name,digest in (("FINAL.md",a.final_sha256),("MANIFEST.json",a.manifest_sha256),("REPORT.md",a.report_sha256)):
        assert len(digest)==64 and sha((root/name).read_bytes())==digest,name
    manifest=json.loads((root/"MANIFEST.json").read_text())
    count=check_payload(root,manifest["files"])
    sources=check_sources(root); direct,sections=check_originals(root,project)
    controls=check_controls(root)
    print(json.dumps(dict(artifact_check="consistent",payload_files=count,source_objects=sources,direct_anchors=direct,original_sections=sections,controls=controls,mathematical_judgment=None),sort_keys=True))
if __name__=="__main__": main()
