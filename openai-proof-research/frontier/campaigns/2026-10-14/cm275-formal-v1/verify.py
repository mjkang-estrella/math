#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. SPDX-License-Identifier: MIT
"""Read-only external-anchor integrity verifier; not a Lean or full-theorem checker.
Path/JSON safeguards adapted from the inspected CM275 contribution verifier.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique(pairs):
    result = {}
    for key, value in pairs:
        need(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def parse(data):
    return json.loads(data, object_pairs_hook=unique)


def safe(name):
    need(isinstance(name,str) and name and '\\' not in name,'bad path')
    path = PurePosixPath(name)
    need(not path.is_absolute() and path.as_posix()==name,'noncanonical path')
    need(all(x not in ('','..','.') for x in path.parts),'unsafe path')
    return name


def verify(root, anchor):
    need(re.fullmatch('[0-9a-f]{64}',anchor) is not None,'bad anchor')
    need(root.is_dir() and not root.is_symlink(),'bad root')
    mp = root/'output-manifest.json'
    need(not mp.is_symlink(),'manifest symlink')
    raw = mp.read_bytes()
    need(sha(raw)==anchor,'external anchor mismatch')
    m = parse(raw)
    need(m['schema']=='CM275-scoped-formal-v1','schema')
    need(m['full_CM275_theorem_formalized'] is False,'full formalization claim')
    expected = {}
    for row in m['files']:
        name=safe(row['path'])
        need(name not in expected and name!='output-manifest.json','duplicate/self payload')
        need(re.fullmatch('[0-9a-f]{64}',row['sha256']) is not None,'payload digest')
        expected[name]=row
    wanted_dirs=[safe(s) for s in m['directories']]
    need(len(wanted_dirs)==len(set(wanted_dirs)),'duplicate directory')
    files,dirs=set(),set()
    for folder,ds,fs in os.walk(root,followlinks=False):
        for name in ds+fs:
            path=Path(folder)/name
            rel=safe(path.relative_to(root).as_posix())
            mode=path.lstat().st_mode
            need(not stat.S_ISLNK(mode),'symlink: '+rel)
            if stat.S_ISDIR(mode): dirs.add(rel)
            else:
                need(stat.S_ISREG(mode),'nonregular payload: '+rel)
                files.add(rel)
    need(files==set(expected)|{'output-manifest.json'},'exact file membership')
    need(dirs==set(wanted_dirs),'exact directory membership')
    for name,row in expected.items():
        data=(root/name).read_bytes()
        need(len(data)==row['bytes'] and sha(data)==row['sha256'],'payload hash: '+name)
    cov=parse((root/'coverage.json').read_bytes())
    build=parse((root/'validation/sealed-build/receipt.json').read_bytes())
    need(cov['full_CM275_theorem_formalized'] is False,'coverage overclaim')
    need(build['full_CM275_theorem_formalized'] is False and build['independent_audit'] is False,'build scope')
    need(build['status']=='PASS scoped source build, exact types, standard axioms and semantic controls','build result')
    for name,digest in build['source_sha256'].items():
        need(sha((root/safe(name)).read_bytes())==digest,'source/build drift: '+name)
    need(cov['source_sha256']==sha((root/'CM275.lean').read_bytes()),'coverage/source drift')
    need((cov['support_theorems'],cov['support_public_declarations'],cov['proved_control_theorems'])==(30,36,14),'counts')
    need(len(build['support_theorems'])==30 and len(build['support_declarations'])==36,'build counts')
    need({r['declaration'] for r in cov['declarations']}=={'CM275.'+n for n in build['support_declarations']},'coverage inventory')
    for group in ['axiom_reports','control_axiom_reports']:
        for name,axioms in build[group].items():
            need(set(axioms)<={'propext','Classical.choice','Quot.sound'},'axiom dependency: '+name)
    sem=parse((root/'validation/sealed-build/semantic-controls/receipt.json').read_bytes())
    need(sem['result']=='PASS_SCOPED_CONTROLS' and sem['mutants']==9 and sem['wrapper_controls']==4,'semantic result')
    for row in sem['rows']:
        if 'sha256' in row:
            need(row['exit_code']!=0,'accepted false goal')
            need(sha((root/'mutants'/safe(row['name'])).read_bytes())==row['sha256'],'mutant drift')
    for row in parse((root/'authentication.json').read_bytes()):
        need(sha((root/'inputs'/(row['directory']+'-manifest.json')).read_bytes())==row['anchor'],'external manifest snapshot')
        need(row['positive_exit']==0 and row['wrong_anchor_exit']!=0,'input integrity controls')
    need(sha((root/'inputs/author-candidate.md').read_bytes())==m['candidate_sha256'],'candidate snapshot')
    need(sha((root/'inputs/author-original-scope.md').read_bytes())==m['scope_sha256'],'scope snapshot')
    return {'result':'PASS_INTEGRITY_ONLY','payloads':len(expected),'directories':len(dirs),
            'support_theorems':30,'support_declarations':36,'controls':14,'false_goal_mutants':9,
            'writes':0,'full_CM275_theorem_formalized':False,'independent_formal_verdict':False}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--anchor',required=True)
    ap.add_argument('--root',type=Path,default=Path(__file__).resolve().parent)
    a=ap.parse_args()
    print(json.dumps(verify(a.root.absolute(),a.anchor),sort_keys=True))

if __name__=='__main__':
    try: main()
    except (ValueError,KeyError,TypeError,OSError) as exc:
        print('INTEGRITY_REJECT: '+str(exc))
        raise SystemExit(1)
