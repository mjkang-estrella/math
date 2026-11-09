#!/bin/bash
set -eu
cd "$(dirname "$0")/.."
rm -f chord-comb4-source.zip
zip -q chord-comb4-source.zip modules.txt src/*.lean scripts/* *.md results.json hashes/*.sha256 regression.json sanity-regression.json
sha256sum chord-comb4-source.zip > source-archive.sha256
