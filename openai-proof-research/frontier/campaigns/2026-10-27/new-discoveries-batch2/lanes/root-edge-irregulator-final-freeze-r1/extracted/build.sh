#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
# Supply the delivered archive and a nonexistent extraction destination.
exec python3 "$HERE/helper_guard.py" python3 "$HERE/verify.py" "$1" "$2"
