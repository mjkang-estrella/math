# Retained implementation attempts

No mathematical frozen proof was edited. Development attempt 1 failed before
Lean compilation: the pin assertion incorrectly required every package to have
a build library directory. Cli is a manifest-pinned dependency with a clean
checkout but no such directory; the original runner omits absent directories.
The corrected pin check asserts all nine revisions/clean tracked trees and
asserts the included runner paths are exactly the available package libraries.

Development attempt 2 rebuilt all 35 mathematical modules with empty logs, but
the audit failed on unsupported `pp.width` and the auxiliary-declaration linter.
Attempt 3 rebuilt them again and audited eight origins before textual private
names with numeric components failed to parse. The final verifier uses actual
environment Name values and `mkIdent`, with the auxiliary linter disabled only
in the audit module. It still kernel-checks each actual declaration and prints
its actual type and axioms. These failed runs are retained under verification/
in the working lane; they are not substituted for the final successful receipt.

Paper attempts: (1) mismatched Tectonic cache layout; (2) a directory bundle
missing its required SHA256SUM; (3) old cache lacked unused mathtools;
(4) old cache lacked a Latin Modern metric; (5) mismatched old format/default
font. The successful build uses installed Tectonic 0.17.0 and a lane-local copy
of its existing cache, only-cached mode, fixed SOURCE_DATE_EPOCH, and TMPDIR
inside this lane. Earlier logs and first-layout overfull diagnostics are in
paper/build/. The final six-page layout removes the long overflowing module
list. One underfull bibliography line is benign and visually inspected.

The first failed Tectonic invocation reported cached bundle URL resolution and
index download attempts despite only-cached mode. No source/registry novelty
refresh was performed here. No browser/account/posting/upload/contact action
was used. This is preparation and does not replace the requested distinct final
review or current novelty adjudication.
