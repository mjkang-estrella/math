from pathlib import Path
R=Path(__file__).resolve().parents[1]
p=R/'scripts/package_source.py';s=p.read_text().replace("files += [R/'inputs/outputs", "files += [R/'paper/manuscript.py']\nfiles += [R/'inputs/outputs");p.write_text(s)
p=R/'replay.py';s=p.read_text().replace("# Hash identity and forbidden-token checks precede any compilation.","""# Hash identity and forbidden-token checks precede any compilation.
for name,digest in json.loads((root/'SOURCE-MANIFEST.json').read_text()).items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
""");p.write_text(s)
# Preserve the completed preliminary replay, then verify the final archive afresh.
(R/'fresh-replay').rename(R/'preliminary-replay')
