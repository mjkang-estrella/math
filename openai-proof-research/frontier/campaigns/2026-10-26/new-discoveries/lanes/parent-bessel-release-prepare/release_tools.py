#!/usr/bin/env python3
"""Conditional release assembly. Never accepts an outcome or edits the ledger."""
from pathlib import Path, PurePosixPath
import argparse, hashlib, io, json, shutil, zipfile

ROOT=Path(__file__).resolve().parents[2]
LANE=ROOT/'lanes/parent-bessel-fejer'
SLUG='bessel-fejer'
GATES=('source','math','formal','novelty','substantive','manuscript')

def digest(data):return hashlib.sha256(data).hexdigest()
def readjson(path):return json.loads(path.read_text())
def safe(name):
    p=PurePosixPath(name)
    if p.is_absolute() or '..' in p.parts or not p.parts:raise ValueError('Unsafe payload path: '+name)
    if p.suffix in ('.olean','.ilean','.pyc'):raise ValueError('Prebuilt proof object: '+name)
    return p

def check_inputs():
    manifest=readjson(LANE/'final-review-hashes.json')
    if len(manifest)!=56:raise ValueError('Expected the reviewed 56-file snapshot; re-review any change')
    for name,expected in manifest.items():
        safe(name);p=LANE/name
        if p.is_symlink() or digest(p.read_bytes())!=expected:raise ValueError('Frozen file changed: '+name)
    audit=readjson(LANE/'verification/parent87-audit.json')
    if audit['status']!='PASS' or audit['declarations']!=87 or len(audit['modules'])!=8:
        raise ValueError('Parent formal checkpoint mismatch')
    if set(audit['axioms'])!={'propext','Classical.choice','Quot.sound'}:raise ValueError('Unexpected proof dependencies')
    for module in audit['modules']:
        if digest((LANE/module['path']).read_bytes())!=module['sha256']:raise ValueError('Module hash mismatch')
    return manifest,audit

def decision_inputs(path):
    decision=readjson(path)
    if decision.get('status')!='ADOPTED_FOR_RELEASE_PENDING_EXTRACTED_REPLAY':
        raise ValueError('Parent must first read and adopt the actual independent final review')
    if any(decision.get('gates',{}).get(g)!='PASS' for g in GATES):raise ValueError('All independent gates required')
    if not decision.get('parent_eligibility_rationale'):raise ValueError('Missing parent substantive decision')
    if decision['reviewed_manifest_sha256']!=digest((LANE/'final-review-hashes.json').read_bytes()):
        raise ValueError('Decision belongs to another review freeze')
    review=Path(decision['review_dir']).resolve()
    for name,key in [('review.md','review_sha256'),('provenance.json','provenance_sha256')]:
        if digest((review/name).read_bytes())!=decision[key]:raise ValueError('Review bytes changed: '+name)
    receipt=review/str(safe(decision['independent_receipt_relative_path']))
    if receipt.read_bytes()!=(LANE/'verification/parent87-audit.json').read_bytes():
        raise ValueError('Independent receipt is not the deterministic replay of this proof; inspect differences')
    return decision,review,receipt

def assemble(decision_path,dest):
    frozen,_=check_inputs();decision,review,receipt=decision_inputs(decision_path)
    if dest.exists():raise ValueError('Canonical destination already exists')
    files=set()
    def copy(src,name):
        target=dest/str(safe(name));target.parent.mkdir(parents=True,exist_ok=True)
        shutil.copyfile(src,target);files.add(name)
    def write(name,text):
        target=dest/str(safe(name));target.parent.mkdir(parents=True,exist_ok=True)
        target.write_text(text);files.add(name)
    for name in frozen:copy(LANE/name,name)
    locations={name:name for name in frozen}
    for name in ['main.tex','paper.pdf','paper-qa.json']:
        copy(LANE/name,'reviewed-originals/'+name);locations[name]='reviewed-originals/'+name
    write('reviewed-parent-hashes.json',json.dumps(frozen,indent=2)+'\n')
    write('reviewed-file-locations.json',json.dumps(locations,indent=2)+'\n')
    for name in ['review.md','provenance.json']+decision.get('review_extras',[]):
        copy(review/str(safe(name)),'reviews/final/'+name)
    copy(decision_path,'reviews/parent-final-decision.json')
    copy(LANE/'verification/parent87-audit.json','verification/parent-audit.json')
    copy(receipt,'verification/independent-audit.json')
    copy(receipt.with_name('Checks.log'),'verification/independent-Checks.log')
    tex=(dest/'main.tex').read_text()
    old='''Independent correctness, novelty and substantive-eligibility review remain
pending. Discovery credit is zero pending those gates, final manuscript review,
and a fresh replay of the extracted proof archive. No worldwide priority is claimed.'''
    new='''Independent final source, mathematical, formal, manuscript, bounded novelty
and substantive-eligibility review passes. Acceptance additionally requires a
fresh replay of the extracted proof archive. No worldwide priority is claimed.'''
    if tex.count(old)!=1:raise ValueError('Review-status overlay no longer matches the reviewed paper')
    write('main.tex',tex.replace(old,new))
    write('README.md','''# Bessel–Fourier kernel counterexample

Read paper.pdf, the formal SourceEndpoint.lean, reviews/final/review.md and the
parent decision. ONE source-conjecture refutation at M=2, alpha=2/5, x=47/50;
no separate existence-conjecture resolution or helper/half-power credit.

Reproduce all 87 declarations in 8 modules with the pinned toolchain/packages:

    python3 verification/verify_candidate.py . --lean-bin /path/to/lean --packages /path/to/.lake/packages

Only propext, Classical.choice and Quot.sound are used. All 56 reviewed originals
are retained with a location map. The release paper changes operational status
only; every Lean/source/verifier byte remains reviewed. Bounded novelty screens
do not establish worldwide priority. The later acceptance.json outside the
immutable archive governs any discovery count. This assembly does not accept it.
''')
    files.add('release-files.json')
    write('release-files.json',json.dumps(sorted(files),indent=2)+'\n')
    print(json.dumps({'status':'ASSEMBLED, NOT ACCEPTED','destination':str(dest),
        'next':'Rebuild release paper, visually inspect all pages and refresh paper-qa.json before archiving'}))

def zip_bytes(payload):
    out=io.BytesIO()
    with zipfile.ZipFile(out,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for name,data in sorted(payload.items()):
            info=zipfile.ZipInfo(SLUG+'/'+name,(2026,10,27,0,0,0));info.external_attr=0o100644<<16
            z.writestr(info,data,compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    return out.getvalue()

def archive(candidate,packet,extraction):
    if packet.exists() or extraction.exists():raise ValueError('Immutable packet/extraction already exists')
    frozen=readjson(candidate/'reviewed-parent-hashes.json');locations=readjson(candidate/'reviewed-file-locations.json')
    if set(frozen)!=set(locations) or len(frozen)!=56:raise ValueError('Reviewed-original location map mismatch')
    for name,expected in frozen.items():
        if digest((candidate/str(safe(locations[name]))).read_bytes())!=expected:raise ValueError('Reviewed bytes lost: '+name)
    audit=readjson(candidate/'verification/parent-audit.json')
    if audit['status']!='PASS' or audit['declarations']!=87 or len(audit['modules'])!=8:raise ValueError('Formal receipt mismatch')
    if (candidate/'verification/parent-audit.json').read_bytes()!=(candidate/'verification/independent-audit.json').read_bytes():
        raise ValueError('Independent proof receipt mismatch')
    for m in audit['modules']:
        if digest((candidate/m['path']).read_bytes())!=m['sha256']:raise ValueError('Proof source drift')
    qa=readjson(candidate/'paper-qa.json')
    if qa.get('pages')!=3 or qa.get('build_issues')!=[] or qa.get('parent_release_all_pages_read') is not True:
        raise ValueError('Fresh release-paper visual QA is required')
    if qa['tex_sha256']!=digest((candidate/'main.tex').read_bytes()) or qa['pdf_sha256']!=digest((candidate/'paper.pdf').read_bytes()):
        raise ValueError('Release-paper QA hashes stale')
    names=readjson(candidate/'release-files.json')
    if names!=sorted(set(names)):raise ValueError('Payload file list is not canonical')
    payload={name:(candidate/str(safe(name))).read_bytes() for name in names}
    manifest={name:digest(data) for name,data in payload.items()}
    payload['MANIFEST.json']=(json.dumps(manifest,indent=2)+'\n').encode()
    data=zip_bytes(payload)
    if data!=zip_bytes(payload):raise ValueError('Archive nondeterministic')
    packet.parent.mkdir(parents=True,exist_ok=True);packet.write_bytes(data)
    with zipfile.ZipFile(packet) as z:
        if z.testzip() is not None:raise ValueError('Archive CRC failure')
        if set(z.namelist())!={SLUG+'/'+n for n in payload}:raise ValueError('Archive membership mismatch')
        for name,blob in payload.items():
            if z.read(SLUG+'/'+name)!=blob:raise ValueError('Archive readback mismatch')
        z.extractall(extraction)
    for name,expected in manifest.items():
        if digest((extraction/SLUG/name).read_bytes())!=expected:raise ValueError('Extracted payload mismatch')
    record={'status':'PASS determinism/manifest/readback; EXTRACTED LEAN REPLAY PENDING; NOT ACCEPTED',
        'packet':str(packet),'sha256':digest(data),'members':len(payload),'payload_files':len(manifest),'extracted':str(extraction/SLUG)}
    (extraction/'readback.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))

def main():
    parser=argparse.ArgumentParser(description=__doc__);sub=parser.add_subparsers(dest='command',required=True)
    sub.add_parser('check-inputs')
    a=sub.add_parser('assemble');a.add_argument('--decision',type=Path,required=True);a.add_argument('--destination',type=Path,required=True)
    a=sub.add_parser('archive');a.add_argument('--candidate',type=Path,required=True);a.add_argument('--packet',type=Path,required=True);a.add_argument('--extraction',type=Path,required=True)
    args=parser.parse_args()
    if args.command=='check-inputs':
        m,a=check_inputs();print(json.dumps({'status':'PASS frozen-input integrity only; independent review pending','files':len(m),'declarations':a['declarations'],'modules':len(a['modules'])}))
    elif args.command=='assemble':assemble(args.decision.resolve(),args.destination.resolve())
    else:archive(args.candidate.resolve(),args.packet.resolve(),args.extraction.resolve())

if __name__=='__main__':main()
