# R023 publication version 1

Author: Myeongjin Kang. No affiliation supplied or displayed.
Paper/original prose: CC BY 4.0. Original code and Lean: MIT.
Third-party dependencies retain their original licenses and notices.

All included proof sources are byte-identical to the independently reviewed
manuscript. In main.tex, changes are limited to front matter (authorship,
license and PDF metadata), removal of historical review-status prose, and
three nonmathematical editorial replacements recorded exactly in
editorial-replacements.json. The mathematical body after reversing those
three replacements is byte-identical to the reviewed body. The exact full
delta is metadata-only.diff. verify_editorial.py checks these claims.
The earlier frozen manuscript and reviews remain in the package. This
publication version has a separate build/visual receipt.

The theorem assumes the pinned OpenAI inputs; the ten Lean support lemmas
do not formalize the full PDE theorem. This is not a full solution to
MathDB 405360. No public submission or DOI is claimed.

Build with Tectonic 0.17.0 in this directory:

    tectonic -X compile main.tex --outdir output/pdf --keep-logs
