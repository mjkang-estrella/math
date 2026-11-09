# Build receipt list (path, sha256, size, file mtime UTC) for every fetched source; HTTP status 200 was
# printed by curl at fetch time (see SUMMARY.md); no file here came from a non-200 response.
import hashlib, json, pathlib, datetime
D = pathlib.Path(__file__).resolve().parents[1]
out = []
for sub in ['sources/abs', 'sources/pdf', 'sources/related', 'sources/registries', 'sources/untrusted-impan', 'sources/untrusted-utu', 'sources/untrusted-uw']:
    for f in sorted((D/sub).glob('*')):
        if f.is_file() and f.name != 'SHA256SUMS':
            b = f.read_bytes()
            out.append({'path': str(f.relative_to(D)), 'sha256': hashlib.sha256(b).hexdigest(), 'bytes': len(b),
                        'mtime_utc': datetime.datetime.fromtimestamp(f.stat().st_mtime, datetime.timezone.utc).isoformat()})
(D/'outputs/source-receipts.json').write_text(json.dumps(out, indent=1))
print(len(out))
