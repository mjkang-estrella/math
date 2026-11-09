"""Summarise HTTP receipts in sources/ (read-only)."""
import json
import pathlib
import sys

d = pathlib.Path(sys.argv[1])
for p in sorted(d.glob('*.receipt.json')):
    r = json.loads(p.read_text())
    print(p.name, '|', r.get('url'), '|', r.get('status'), '|', r.get('bytes'),
          '|', (r.get('sha256') or '')[:16], '|', r.get('utc', '')[:19], '|',
          r.get('final_url') if r.get('final_url') != r.get('url') else '', '|', r.get('error', ''))
