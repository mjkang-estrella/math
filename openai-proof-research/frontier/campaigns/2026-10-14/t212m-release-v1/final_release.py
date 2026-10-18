#!/usr/bin/env python3
"""Preparatory selection and fail-closed T212M release assembly. MIT; Myeongjin Kang."""
import argparse
import json
from pathlib import Path
import sys
from release_common import *
HERE = Path(__file__).absolute().parent
BUNDLE = 'BUNDLE-MANIFEST.json'
IMPL = 'IMPLEMENTATION-MANIFEST.json'

def encoded(value):
    return (json.dumps(value, sort_keys=True, indent=2) + '\n').encode()

def payload(campaign, implementation_anchor, final=False, r2=None, closure=None):
    policy, selection = implementation(lambda n:read(HERE,n), implementation_anchor)
    rows = validate_inputs(lambda n:read(campaign,n), selection, policy, final, r2, closure)
    result = {r['path']:read(campaign,r['path']) for r in rows}
    result.update({n:read(HERE,n) for n in OWN + [IMPL]})
    result['README.md'] = result['RELEASE-README.md']
    manifest = {'schema':'T212M-selected-bundle-v1',
                'status':'REVIEW_CLOSED_CONDITIONAL_RELEASE' if final else 'PREPARATION_NOT_FINAL',
                'implementation_anchor':implementation_anchor,
                'r2_anchor':r2 if final else None, 'closure_anchor':closure if final else None,
                'accepted':False, 'published':False, 'count_change':0,
                'files':{n:record(b) for n,b in sorted(result.items())},
                'directories':dirs_for(result)}
    result[BUNDLE] = encoded(manifest)
    return result

def verify(data, actual_dirs, manifest_anchor, implementation_anchor, final=False,
           r2=None, closure=None):
    anchor(manifest_anchor)
    require(sha(data[BUNDLE]) == manifest_anchor, 'external bundle manifest anchor mismatch')
    m = parse(data[BUNDLE])
    require(set(m) == {'schema','status','implementation_anchor','r2_anchor','closure_anchor',
                      'accepted','published','count_change','files','directories'}, 'bundle schema keys')
    require(m['schema'] == 'T212M-selected-bundle-v1' and
            m['status'] == ('REVIEW_CLOSED_CONDITIONAL_RELEASE' if final else 'PREPARATION_NOT_FINAL'),
            'bundle status mismatch')
    require(m['implementation_anchor'] == implementation_anchor and m['accepted'] is False
            and m['published'] is False and type(m['count_change']) is int and m['count_change']==0,
            'bundle boundary/implementation mismatch')
    require(m['r2_anchor'] == (r2 if final else None) and
            m['closure_anchor'] == (closure if final else None), 'bundle completion anchor mismatch')
    require(set(data) == set(m['files']) | {BUNDLE}, 'exact bundle file inventory mismatch')
    require(m['directories'] == dirs_for(data) and actual_dirs == m['directories'],
            'exact directory inventory mismatch')
    for n,b in data.items():
        public(n)
        if n != BUNDLE:
            check(b,m['files'][n])
    policy,selection = implementation(data.__getitem__,implementation_anchor)
    rows=validate_inputs(data.__getitem__,selection,policy,final,r2,closure)
    expected={r['path'] for r in rows}|set(OWN)|{IMPL,BUNDLE,'README.md'}
    require(set(data)==expected, 'selection differs from exact public inventory')
    require(data['README.md']==data['RELEASE-README.md'], 'top README mismatch')
    return {'status':'PASS_EXACT_PUBLIC_IDENTITY', 'preparation_only':not final,
            'files':len(data), 'selected_evidence_files':len(rows),
            'bundle_manifest_sha256':manifest_anchor, 'accepted':False, 'published':False}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('command',choices=['preflight','stage','assemble','verify'])
    p.add_argument('--implementation-anchor',required=True)
    p.add_argument('--campaign',type=Path)
    p.add_argument('--output',type=Path)
    p.add_argument('--input',type=Path)
    p.add_argument('--manifest-anchor')
    p.add_argument('--final',action='store_true',help='verify actual review-closed release')
    p.add_argument('--r2-anchor');p.add_argument('--closure-anchor')
    a=p.parse_args()
    if a.command=='verify':
        require(a.input is not None and a.manifest_anchor is not None,'input/manifest anchor required')
        ancestry(a.input)
        if stat.S_ISDIR(a.input.lstat().st_mode):
            data,ds=tree(a.input)
        else:
            data=zip_payload(a.input);ds=dirs_for(data)
        print(json.dumps(verify(data,ds,a.manifest_anchor,a.implementation_anchor,
                               a.final,a.r2_anchor,a.closure_anchor),indent=2));return
    require(not a.final, '--final is only a verification flag; assemble is intrinsically final')
    require(a.campaign is not None,'absolute campaign directory required')
    ancestry(a.campaign)
    data=payload(a.campaign,a.implementation_anchor,a.command=='assemble',a.r2_anchor,a.closure_anchor)
    ma=sha(data[BUNDLE])
    verify(data,dirs_for(data),ma,a.implementation_anchor,a.command=='assemble',a.r2_anchor,a.closure_anchor)
    if a.command=='preflight':
        require(a.output is None,'preflight does not write output')
        print(json.dumps({'status':'PASS_PREPARATORY_SELECTION_ONLY','selected_evidence_files':
                          len(parse(data['public-selection-final-draft.json'])['files']),
                          'final_assembly_available':False},indent=2));return
    require(a.output is not None,'new output required')
    new_output(a.output,[a.campaign,HERE])
    if a.command=='stage':
        a.output.mkdir()
        for n,b in sorted(data.items()):
            dest=a.output.joinpath(*safe(n).parts);dest.parent.mkdir(parents=True,exist_ok=True)
            with dest.open('xb') as f:f.write(b)
        actual,ds=tree(a.output)
        receipt=verify(actual,ds,ma,a.implementation_anchor)
    else:
        stable_zip(a.output,data)
        actual=zip_payload(a.output)
        receipt=verify(actual,dirs_for(actual),ma,a.implementation_anchor,True,a.r2_anchor,a.closure_anchor)
        receipt['zip_sha256']=sha(read(a.output.parent,a.output.name))
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':
    try:main()
    except (ValueError,OSError,KeyError,TypeError,zipfile.BadZipFile) as e:
        print('REFUSED: '+str(e),file=sys.stderr);sys.exit(1)
