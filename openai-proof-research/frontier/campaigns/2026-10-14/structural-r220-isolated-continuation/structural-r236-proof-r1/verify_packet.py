#!/usr/bin/env python3
"""Read-only, explicit-anchor verifier for this exact selected packet.
No traversal, writes, network access, mathematical tests, or inherited manifests.
"""
import argparse, hashlib, json, stat
from pathlib import Path

def digest(b): return hashlib.sha256(b).hexdigest()
def require(ok, message):
    if not ok: raise ValueError(message)
def verify(root, manifest_anchor, final_anchor, selection_name, selection_anchor, report_anchor=None):
    root=Path(root).resolve(strict=True)
    def read(rel):
        p=Path(rel)
        require(not p.is_absolute() and '..' not in p.parts and p.as_posix()==rel, 'noncanonical selected path')
        q=root
        for part in p.parts:
            q=q/part
            require(not q.is_symlink(), 'symlink in selected path')
        require(q.resolve(strict=True).is_relative_to(root), 'path escapes exact root')
        require(q.is_file(), 'selected item not a regular file')
        return q,q.read_bytes()
    _,mb=read('MANIFEST.json');require(digest(mb)==manifest_anchor,'manifest anchor mismatch')
    _,sb=read(selection_name);require(digest(sb)==selection_anchor,'selection anchor mismatch')
    selected=json.loads(sb)['paths'];require(len(selected)==len(set(selected)),'duplicate selection')
    entries=json.loads(mb)['entries'];paths=[x['path'] for x in entries]
    require(len(paths)==len(set(paths)) and sorted(paths)==sorted(selected),'manifest is not the exact explicit selection')
    require(selection_name in selected and 'FINAL.md' in selected,'missing selected anchor file')
    for row in entries:
        p,b=read(row['path'])
        require(len(b)==row['bytes'] and digest(b)==row['sha256'],'selected bytes mismatch: '+row['path'])
        require(stat.S_IMODE(p.stat().st_mode)==int(row['mode'],8),'selected mode mismatch: '+row['path'])
    _,fb=read('FINAL.md');require(digest(fb)==final_anchor,'FINAL anchor mismatch')
    require('MANIFEST.json' not in selected and 'REPORT.md' not in selected,'detached files included recursively')
    if report_anchor is not None:
        _,rb=read('REPORT.md');require(digest(rb)==report_anchor,'outside REPORT anchor mismatch')
    return {'artifact_verification':'exact selection, bytes, modes and explicit anchors verified','selected_files':len(entries),'mathematical_grade':None}

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--root',required=True)
    ap.add_argument('--manifest-sha256',required=True);ap.add_argument('--final-sha256',required=True)
    ap.add_argument('--selection',required=True);ap.add_argument('--selection-sha256',required=True)
    ap.add_argument('--report-sha256');a=ap.parse_args()
    try: print(json.dumps(verify(a.root,a.manifest_sha256,a.final_sha256,a.selection,a.selection_sha256,a.report_sha256),sort_keys=True))
    except (ValueError,OSError,KeyError,TypeError,json.JSONDecodeError) as e:
        ap.exit(1,'artifact verification rejected: '+str(e)+'\n')
