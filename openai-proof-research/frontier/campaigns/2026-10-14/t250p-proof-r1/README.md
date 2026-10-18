# t250p-proof-r1

Independent full-proof gate for frozen T250P. Verdict and objections: review.md. Identity and replay record: identity-checks.json. This directory contains no third-party bodies.

Verify against the manifest SHA256 that the reviewer reported externally:

    python3 -B verify.py EXTERNAL_MANIFEST_SHA256

Run control-tests.py only from a disposable copy. It writes scratch files only under a new /var/tmp directory and removes them afterwards. The verifier never reseals. Original prose CC BY 4.0, scripts MIT.
