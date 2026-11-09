import sys, json, pathlib, hashlib, datetime, subprocess, time
import requests

ROOT = pathlib.Path(__file__).resolve().parents[1]
out = ROOT / 'sources'
log = out / 'retrievals.json'
records = json.loads(log.read_text()) if log.exists() else []
for name, url in json.loads(pathlib.Path(sys.argv[1]).read_text()):
    record = {'name': name, 'url': url, 'retrieved_utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        r = requests.get(url, timeout=35)
        p = out / name
        p.write_bytes(r.content)
        record.update(status=r.status_code, final_url=r.url, content_type=r.headers.get('Content-Type'), bytes=len(r.content), sha256=hashlib.sha256(r.content).hexdigest(), path=str(p.relative_to(ROOT)))
        if r.status_code == 200 and r.content.startswith(b'%PDF'):
            textpath = p.with_suffix('.txt')
            proc = subprocess.run(['pdftotext', '-layout', str(p), str(textpath)], capture_output=True, text=True)
            record.update(extraction_exit=proc.returncode, extraction_stderr=proc.stderr)
        print(name, r.status_code, len(r.content), flush=True)
        if r.status_code == 429:
            record['stopped_for_rate_limit'] = True
            records.append(record)
            log.write_text(json.dumps(records, indent=2))
            break
    except Exception as e:
        record['error'] = str(e)
        print(name, str(e), flush=True)
    records.append(record)
    log.write_text(json.dumps(records, indent=2))
    time.sleep(1)
