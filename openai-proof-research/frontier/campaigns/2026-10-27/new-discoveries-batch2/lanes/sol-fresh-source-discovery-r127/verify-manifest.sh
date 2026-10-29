#!/bin/sh
set -eu
HERE=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
exec python "$HERE/../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py" python "$HERE/work.py" verify
