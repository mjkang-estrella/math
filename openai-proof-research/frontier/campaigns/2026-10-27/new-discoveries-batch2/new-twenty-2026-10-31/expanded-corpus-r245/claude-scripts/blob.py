"""Decode a GitHub git-blob API JSON body (base64) and print it, optionally the first K chars (read-only)."""
import base64
import json
import sys

j = json.load(open(sys.argv[1], encoding='utf-8'))
txt = base64.b64decode(j['content']).decode('utf-8', 'replace')
K = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
print('sha', j.get('sha'), 'size', j.get('size'))
print(txt[:K])
