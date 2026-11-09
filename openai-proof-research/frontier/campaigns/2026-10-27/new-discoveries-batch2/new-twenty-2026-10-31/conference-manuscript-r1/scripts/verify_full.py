"""Compare the safely extracted full dossier with its manifest and with the lane files.
   python3 -I -B scripts/verify_full.py"""
import datetime, hashlib, json, os
sha = lambda p: hashlib.sha256(open(p, 'rb').read()).hexdigest()
man = json.load(open('full-dossier-manifest.json'))
ext = json.load(open('tmp/verify-full-extraction.json'))
m = {e['name']: e['sha256'] for e in man['entries']}
x = {e['name']: e['sha256'] for e in ext['files']}
lane = {n: sha(n) for n in m}
rec = {'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(), 'archive': man['archive'],
       'archive_sha256': sha(man['archive']), 'manifest_sha256_matches': sha(man['archive']) == man['sha256'],
       'safe_extraction': ext['safe'], 'members': len(x), 'extracted_equals_manifest': m == x,
       'manifest_equals_current_lane_files': m == lane,
       'pdf_inside_equals_lane_pdf': x.get('conference-324342-draft.pdf') == sha('conference-324342-draft.pdf'),
       'source_zip_inside_equals_lane': x.get('conference-324342-source.zip') == sha('conference-324342-source.zip'),
       'lean_zip_inside': x.get('dossier/lean/324342-replay-fit-source.zip'),
       'extracted_to': 'tmp/verify-full'}
rec['PASS'] = all(rec[k] for k in ('manifest_sha256_matches', 'safe_extraction', 'extracted_equals_manifest',
                                   'manifest_equals_current_lane_files', 'pdf_inside_equals_lane_pdf',
                                   'source_zip_inside_equals_lane')) and \
    rec['lean_zip_inside'] == 'c6977a39d3f5aa81122c6ad9c2d374bcadc281dccf577208fbda31eac2e1a00f'
json.dump(rec, open('full-dossier-verification.json', 'w'), indent=1)
arch = {n: sha(n) for n in ('conference-324342-draft.pdf', 'conference-324342-source.zip',
                            'conference-324342-full-dossier.zip', 'dossier/lean/324342-replay-fit-source.zip')}
json.dump(arch, open('ARCHIVES-SHA256.json', 'w'), indent=1)
print('PASS', rec['PASS'], rec['members'], 'members'); print(json.dumps(arch, indent=1))
