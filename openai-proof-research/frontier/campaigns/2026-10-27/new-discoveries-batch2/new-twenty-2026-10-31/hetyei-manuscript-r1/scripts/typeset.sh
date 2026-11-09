#!/bin/bash
set -euo pipefail
# Drop ms-only registers/strings. The plain roff layout defines the used macros.
sed '/^\.nr /d; /^\.ds /d; s/^\.SH$/.SH/; s/^\.bp$/.bp\n.sp 0.45i/' manuscript.ms > tmp/body.roff
groff -t -Tps scripts/layout.roff tmp/body.roff > manuscript.ps
ps2pdf -sPAPERSIZE=letter manuscript.ps manuscript.pdf
