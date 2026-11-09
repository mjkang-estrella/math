#!/bin/bash
# Single-pass ID-only word search across all openai-proof-research files (md/json/tex/txt/lean), excluding corpus chunks, .lake and this lane.
F=/home/mj-kang/Documents/Dev/math/openai-proof-research
grep -rwoF -f "$(dirname "$0")/ids.txt" "$F" --include=*.md --include=*.json --include=*.tex --include=*.txt --include=*.lean --exclude-dir=corpus --exclude-dir=expanded-corpus-r114 --exclude-dir=.lake 2>/dev/null | sort -u
