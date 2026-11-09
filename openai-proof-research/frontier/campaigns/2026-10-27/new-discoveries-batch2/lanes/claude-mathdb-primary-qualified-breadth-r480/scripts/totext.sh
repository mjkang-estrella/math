#!/bin/bash
for f in "$1"/*.pdf; do pdftotext -layout "$f" "${f%.pdf}.txt" 2>>"$1/../pdftotext-stderr.txt" || echo "FAIL $f" >> "$1/../pdftotext-stderr.txt"; done
