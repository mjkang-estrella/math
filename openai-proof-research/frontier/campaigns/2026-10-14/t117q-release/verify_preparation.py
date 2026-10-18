#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Read-only pending preparation verification; not a review or final release gate."""
from pathlib import Path
import sys
sys.dont_write_bytecode = True
from bundle_common import public_path, EXPECTED_ANCHORS, check, parse, read, require, sha
HERE=Path(__file__).resolve().parent
ROOT=HERE if (HERE/'frontier').is_dir() else HERE.parents[3]
PREFIX='frontier/campaigns/2026-10-14/'

def main():
    selection=parse(read(HERE,'payload-selection.json'))
    prep=parse(read(HERE,'preparation.json'))
    require(prep['status']=='PREPARED_PENDING_MANUSCRIPT_REVIEW','preparation status changed')
    require(prep['anchors']==EXPECTED_ANCHORS,'preparation anchors changed')
    require(EXPECTED_ANCHORS['t117q-manuscript-review-r1'] is None,'pending preparation must be re-reviewed after manuscript adoption')
    manifests={}
    for packet,entry in EXPECTED_ANCHORS.items():
        if entry is None: continue
        raw=read(ROOT,PREFIX+packet+'/'+entry['file'])
        require(sha(raw)==entry['sha256'],'external packet anchor mismatch: '+packet)
        manifests[packet]=parse(raw)
    names=set()
    for row in selection['files']:
        name=row['path'];public_path(name);require(name not in names,'duplicate selected path');names.add(name)
        require(name.startswith(PREFIX),'selection outside campaign')
        packet,rel=name[len(PREFIX):].split('/',1)
        require(packet in manifests, 'selected packet lacks frozen anchor')
        require('private' not in Path(rel).parts,'private body selected')
        data=read(ROOT,name);check(data,row)
        if packet in manifests and rel!=EXPECTED_ANCHORS[packet]['file']:
            files=manifests[packet]['files']
            entry=files[rel] if isinstance(files,dict) else next(x for x in files if x['path']==rel)
            require(entry['sha256']==row['sha256'] and entry['bytes']==row['bytes'],'selected file not bound by frozen packet: '+name)
    for packet,entry in EXPECTED_ANCHORS.items():
        if entry is not None:require(PREFIX+packet+'/'+entry['file'] in names,'missing selected anchor')
    print('PREPARATION IDENTITIES VERIFIED:',len(names),'selected files; manuscript pending; no acceptance')

if __name__=='__main__':
    try:main()
    except (OSError,ValueError,KeyError,TypeError,StopIteration) as exc:sys.exit('PREPARATION REFUSED: '+str(exc))
