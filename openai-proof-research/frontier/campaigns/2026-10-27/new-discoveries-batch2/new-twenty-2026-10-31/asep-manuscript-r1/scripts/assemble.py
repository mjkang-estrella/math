"""Lane tooling (not part of the dossier).

    python3 -I assemble.py source      -> asep-368807-source.zip from dossier/ (after make_manifest.py)
    python3 -I assemble.py full        -> full/ tree, full-dossier-manifest.json, asep-368807-full-dossier.zip

Copies of frozen inputs are byte-identical (verified against receipts/frozen-before.json).
ZIPs are deterministic: sorted members, fixed timestamp, mode 0644.
"""
import hashlib, json, shutil, sys, zipfile
from pathlib import Path

L = Path(__file__).resolve().parents[1]
BASE = L.parent
STAMP = (2026, 11, 2, 0, 0, 0)
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

FROZEN_COPIES = {  # destination in full/ : frozen source (relative to new-twenty-2026-10-31)
    'sources/arxiv-2506.10671v1.pdf': 'expanded-corpus-r96/sources/368807-pdf.pdf',
    'sources/arxiv-2506.10671v1.pdf.receipt.json': 'expanded-corpus-r96/sources/368807-pdf-receipt.json',
    'sources/arxiv-2506.10671v1.txt': 'expanded-corpus-r96/sources/368807-pdf.txt',
    'sources/arxiv-2506.10671-html.receipt.json': 'expanded-corpus-r96/sources/368807-receipt.json',
    'sources/arxiv-2506.10671-abs.html': 'asep-review-r1/downloads/arxiv-2506.10671-abs.html',
    'sources/arxiv-2506.10671-abs.html.receipt.json': 'asep-review-r1/receipts/arxiv-2506.10671-abs.html.receipt.json',
    'sources/arxiv-math0512493v1.pdf': 'asep-review-r1/downloads/arxiv-math0512493.pdf',
    'sources/arxiv-math0512493v1.pdf.receipt.json': 'asep-review-r1/receipts/arxiv-math0512493.pdf.receipt.json',
    'sources/arxiv-math0512493-abs.html': 'asep-review-r1/downloads/arxiv-math0512493-abs.html',
    'sources/arxiv-math0512493-abs.html.receipt.json': 'asep-review-r1/receipts/arxiv-math0512493-abs.html.receipt.json',
    'sources/arxiv-2507.07003v3.pdf': 'asep-review-r1/downloads/arxiv-2507.07003.pdf',
    'sources/arxiv-2507.07003v3.pdf.receipt.json': 'asep-review-r1/receipts/arxiv-2507.07003.pdf.receipt.json',
    'sources/optimization-online-AF-2026-08.pdf': 'asep-review-r1/downloads/optimization-online-AF-2026-08.pdf',
    'sources/optimization-online-AF-2026-08.pdf.receipt.json': 'asep-review-r1/receipts/optimization-online-AF-2026-08.pdf.receipt.json',
    'sources/optimization-online-2024-03-landing.html': 'asep-review-r1/downloads/oo-2024-03-landing.html',
    'sources/optimization-online-2024-03-landing.html.receipt.json': 'asep-review-r1/receipts/oo-2024-03-landing.html.receipt.json',
    'sources/unipv-thesis-vercesi-2023.pdf': 'asep-review-r1/downloads/unipv-thesis.pdf',
    'sources/unipv-thesis-vercesi-2023.pdf.receipt.json': 'asep-review-r1/receipts/unipv-thesis.pdf.receipt.json',
    'sources/arxiv-2511.05045.pdf': 'expanded-corpus-r96/sources/prior/368807-2511.05045.pdf',
    'sources/arxiv-2511.05045.pdf.receipt.json': 'expanded-corpus-r96/sources/prior/368807-2511.05045.pdf-receipt.json',
    'history/ASEP-COUNTEREXAMPLE.md': 'expanded-corpus-r96/ASEP-COUNTEREXAMPLE.md',
    'history/lean-replay-3-result.json': 'expanded-corpus-r96/lean-replay-3/result.json',
    'history/perm-order.txt': 'expanded-corpus-r96/lean/perm-order.txt',
    'review/asep-review-r1-review.json': 'asep-review-r1/review.json',
    'review/asep-review-r1-REVIEW.md': 'asep-review-r1/REVIEW.md',
    'review/asep-review-r1-rv-n5-table2.json': 'asep-review-r1/outputs/rv-n5-table2.json',
    'review/asep-review-r1-rv-n4.json': 'asep-review-r1/outputs/rv-n4.json',
    'review/asep-review-r1-rv-n8.json': 'asep-review-r1/outputs/rv-n8.json',
    'review/asep-review-r1-rv-n7-probe.json': 'asep-review-r1/outputs/rv-n7-probe.json',
    'review/asep-root-adjudication-r1.json': 'asep-root-adjudication-r1.json',
}
LANE_COPIES = {  # destination in full/ : lane path
    'asep-368807-draft.pdf': 'asep-368807-draft.pdf',
    'asep-368807-source.zip': 'asep-368807-source.zip',
    'receipts': 'receipts',
    'qa': 'qa',
    'fresh-replay': 'fresh-replay/receipts',
}


def zipdir(root, out):
    files = sorted(p for p in Path(root).rglob('*') if p.is_file() and '__pycache__' not in p.parts)
    with zipfile.ZipFile(out, 'w', zipfile.ZIP_DEFLATED, compresslevel=9) as z:
        for p in files:
            zi = zipfile.ZipInfo(str(p.relative_to(root)), STAMP)
            zi.external_attr = 0o100644 << 16
            zi.compress_type = zipfile.ZIP_DEFLATED
            z.writestr(zi, p.read_bytes())
    return len(files)


def main():
    mode = sys.argv[1]
    if mode == 'source':
        n = zipdir(L / 'dossier', L / 'asep-368807-source.zip')
        print(n, sha(L / 'asep-368807-source.zip'))
        return
    assert mode == 'full'
    frozen = json.loads((L / 'receipts' / 'frozen-before.json').read_text())['files']
    full = L / 'full'
    if full.exists():
        shutil.rmtree(full)
    shutil.copytree(L / 'dossier', full / 'dossier')
    for dst, src in FROZEN_COPIES.items():
        t = full / dst
        t.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(BASE / src, t)
        assert sha(t) == frozen[src], src
    for dst, src in LANE_COPIES.items():
        s = L / src
        if s.is_dir():
            shutil.copytree(s, full / dst)
        else:
            shutil.copyfile(s, full / dst)
    files = {str(p.relative_to(full)): sha(p) for p in sorted(full.rglob('*')) if p.is_file()}
    man = {'description': 'SHA-256 of every member of asep-368807-full-dossier.zip (except this manifest)',
           'frozen_copies': FROZEN_COPIES, 'files': files}
    (full / 'full-dossier-manifest.json').write_text(json.dumps(man, indent=1) + '\n')
    shutil.copyfile(full / 'full-dossier-manifest.json', L / 'full-dossier-manifest.json')
    n = zipdir(full, L / 'asep-368807-full-dossier.zip')
    print(n, sha(L / 'asep-368807-full-dossier.zip'))


if __name__ == '__main__':
    main()
