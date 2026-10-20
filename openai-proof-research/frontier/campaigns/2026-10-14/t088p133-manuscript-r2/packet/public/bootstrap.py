#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Install pinned TeX engine only under the manuscript root; no global install."""
from pathlib import Path
import hashlib,io,tarfile,urllib.request
root=Path(__file__).resolve().parents[2]
u='https://github.com/tectonic-typesetting/tectonic/releases/download/tectonic%400.17.0/tectonic-0.17.0-x86_64-unknown-linux-musl.tar.gz'
archive='8533d07f9ccbd7a65824b9e0459041bca34af1eb33daba48f59215593753a3b7'
binary='a98aa59ad5c1df39a6c9e56cbfc5088f2b11d6c179c0130b97998e4bd46a46da'
target=root/'tools/tectonic';target.parent.mkdir(exist_ok=True)
if target.exists() and hashlib.sha256(target.read_bytes()).hexdigest()==binary:
 print('Existing pinned Tectonic binary matches');raise SystemExit(0)
b=urllib.request.urlopen(u).read();assert hashlib.sha256(b).hexdigest()==archive
with tarfile.open(fileobj=io.BytesIO(b)) as t:data=t.extractfile('tectonic').read()
assert hashlib.sha256(data).hexdigest()==binary
target.write_bytes(data);target.chmod(0o755)
print('Installed authenticated Tectonic 0.17.0 under',target.parent)
