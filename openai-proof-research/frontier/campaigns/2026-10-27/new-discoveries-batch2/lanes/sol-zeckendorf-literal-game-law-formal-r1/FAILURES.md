# Preserved failures and limitations

All attempt-*.log and attempt-*.json are append-only evidence, including failures.
Initial broad Mathlib.Tactic import exceeded group RSS2800MiB and was killed;
no cap was raised. Narrow imports compile within the original exception.
Subsequent failed attempts preserve arithmetic-expression normalization errors,
unused-tactic warnings treated as errors, an unavailable multiset lemma,
a missing rewrite and a finite API probe containing unavailable declarations.
Corrections use direct multiset induction and ordinary arithmetic; no axiom,
sorry, unsafe, native_decide, generated partial proof or weakened compiler flags.

The first exhaustive audit generator used textual #check names, which failed on
private numeric name components. Its failed log is retained. The corrected audit
uses Lean.mkIdent on actual environment Names, so private/generated declarations
are checked rather than skipped.

First source-only extraction replay failed before compiling with IndexError:
package.py read sys.argv[1] while imported without an extra argument. The failed
extraction replay/fresh-a is preserved. The import guard was fixed, a new archive
was built, and replay/fresh-c and fresh-d are fresh successful-replay targets.
The obsolete first extraction is failure evidence, not the certified archive.

Terminal uniqueness/Z(N) bridge and actual normalized P_N product-law interfaces
remain unimplemented. This is a substantive incomplete mandatory gate, not an
access-blocked proof, timing estimate, or negative mathematical result.
