"""Build a deterministic source-only ZIP, suitable for arXiv preparation."""
from pathlib import Path
import hashlib
import json
from zipfile import ZIP_DEFLATED, ZipFile, ZipInfo

ROOT = Path(__file__).resolve().parent
FILES = ['main.tex', 'references.tex'] + sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / 'sections').glob('*.tex'))
archive = ROOT / 'output/prime-predecessor-arxiv-source.zip'
archive.parent.mkdir(parents=True, exist_ok=True)
with ZipFile(archive, 'w', compression=ZIP_DEFLATED, compresslevel=9) as out:
    for name in FILES:
        info = ZipInfo(name, date_time=(2026, 10, 9, 0, 0, 0))
        info.compress_type = ZIP_DEFLATED
        info.external_attr = 0o644 << 16
        out.writestr(info, (ROOT / name).read_bytes())
manifest = {name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest() for name in FILES}
(ROOT / 'evidence/authored-source-manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(f'Packaged {len(FILES)} LaTeX files: {archive}')
