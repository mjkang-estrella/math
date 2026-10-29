# Failures and access limits

* Initial context-summary scanner used frontier as its root, yielding zero
  summaries. Preserved context-screen-wrong-root.json; corrected to repository
  root and re-ran under identical caps:315 summaries. No novelty clearance was
  inferred from the bad scan.
* UAb exact public repository body returned HTTP403. Direct MO HTML returned
  HTTP403, although web public extraction supplied the question/answer proof.
  No direct retry or access bypass occurred.
* Web requested follow-up HTMLv3 and received404; inspected actual abstract
  next, which lists onlyv1, and retrieved that exactv1 PDF. Failed guessedv3 is
  not claimed to exist. A guessed incomplete Cambridge article route and DOI
  web lookup failed. VoR body equivalence remains unknown.
* First accepted-manuscript download and PDF extraction were performed as
  direct curl and capped pdftotext; the guard output is in the tool transcript,
  not a local receipt. All later scripts/fetch/extraction/checks used retained
  copied caps. No mathematical experiment ran without the guard.
* No numerical/CPU/RSS failures or raised caps. Fetch/prepare/check receipts
  retained. No GitHub API call was made; inherited403/429 restrictions respected.
* Source page search-engine crawl labels such as 'months ago' are not used
  as publication dates. arXiv histories and PDF imprints identify versions.
