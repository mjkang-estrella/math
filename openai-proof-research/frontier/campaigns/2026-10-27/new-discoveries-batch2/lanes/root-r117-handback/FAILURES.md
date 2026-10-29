Root's first verifier mistakenly read the retained original sha256 field from
frozen-after.json instead of after_sha256, so it observed no drift and failed its
assertion. The worker schema was then read directly and the key corrected. No
worker record or hash baseline was changed. The failed tool result is preserved
in the conversation; no PASS was inferred from it.
