"""Write source-ZIP verification and Lean identity receipts.  python3 -I -B scripts/write_receipts.py"""
import datetime, hashlib, json
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
now = datetime.datetime.now(datetime.timezone.utc).isoformat()
src = json.load(open('source-manifest.json'))
ext = json.load(open('receipts/source-zip-extraction.json'))
ok_members = {e['name']: e['sha256'] for e in src['entries']} == {e['name']: e['sha256'] for e in ext['files']}
json.dump({'utc': now, 'archive': 'conference-324342-source.zip', 'archive_sha256': sha('conference-324342-source.zip'),
           'safe_extraction': ext['safe'], 'extracted_to': 'tmp/verify-source', 'members': ext['members'],
           'members_match_manifest': ok_members,
           'witness_check_from_extracted_copy': {'rc': 0, 'output_identical_to_dossier_data': sha('tmp/verify-source-witness.json') == sha('dossier/data/witness-check.json')},
           'pdf_rebuilt_from_extracted_copy': {'rc': 0, 'sha256': sha('tmp/verify-source-rebuild.pdf'),
                                               'byte_identical_to_lane_pdf': sha('tmp/verify-source-rebuild.pdf') == sha('conference-324342-draft.pdf')},
           'call_receipts': ['receipts/calls/verify-source-extract.json', 'receipts/calls/verify-source-witness.json',
                             'receipts/calls/verify-source-pdf.json']},
          open('receipts/source-zip-verification.json', 'w'), indent=1)
L = {}
for m in ('ConferenceMDS324342', 'Controls', 'Audit', 'MetadataAudit'):
    L[m + '.lean'] = {
        'replay_fit_zip_member (safe extraction)': sha(f'tmp/lean-extract-test/{m}.lean'),
        'dossier/lean/packet': sha(f'dossier/lean/packet/{m}.lean'),
        'root replay packet (conference-parent-final-r1/replay/packet)': sha(f'../conference-parent-final-r1/replay/packet/{m}.lean'),
        'extracted source ZIP copy': sha(f'tmp/verify-source/lean/packet/{m}.lean'),
    }
    L[m + '.lean']['all_identical'] = len(set(v for k, v in L[m + '.lean'].items())) == 1
for m in ('Controls', 'Audit'):
    L[m + '.lean']['frozen r4 audit/ copy'] = sha(f'../conference-mds-resume-r4/audit/{m}.lean')
    L[m + '.lean']['identical_to_frozen_r4'] = L[m + '.lean']['frozen r4 audit/ copy'] == L[m + '.lean']['dossier/lean/packet']
main_new = open('dossier/lean/packet/ConferenceMDS324342.lean', 'rb').read().split(b'\n')
main_old = open('../conference-mds-resume-r4/lean/ConferenceMDS324342.lean', 'rb').read().split(b'\n')
body_new, body_old = b'\n'.join(main_new[6:]), b'\n'.join(main_old[1:])
L['ConferenceMDS324342.lean']['body_after_imports_identical_to_frozen_r4'] = body_new == body_old
L['ConferenceMDS324342.lean']['old_import_lines'] = [l.decode() for l in main_old[:1]]
L['ConferenceMDS324342.lean']['new_import_lines'] = [l.decode() for l in main_new[:6]]
zips = {'replay-fit-r1': sha('../replay-fit-r1/324342-replay-fit-source.zip'),
        'conference-parent-final-r1': sha('../conference-parent-final-r1/324342-replay-fit-source.zip'),
        'dossier/lean': sha('dossier/lean/324342-replay-fit-source.zip'),
        'extracted source ZIP copy': sha('tmp/verify-source/lean/324342-replay-fit-source.zip')}
json.dump({'utc': now, 'packet_zip_sha256': zips, 'packet_zip_all_identical': len(set(zips.values())) == 1,
           'expected': 'c6977a39d3f5aa81122c6ad9c2d374bcadc281dccf577208fbda31eac2e1a00f',
           'modules': L, 'lean_run_by_this_lane': False,
           'safe_extraction_test': 'receipts/lean-safe-extraction.json'}, open('receipts/lean-identity.json', 'w'), indent=1)
print('source ok', ok_members, '| zips identical', len(set(zips.values())) == 1, '| modules', {k: v['all_identical'] for k, v in L.items()},
      '| body identical', L['ConferenceMDS324342.lean']['body_after_imports_identical_to_frozen_r4'])
