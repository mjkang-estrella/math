from pathlib import Path
r=Path(__file__).resolve().parents[1];p=r/'packet/public';old=r.parent/'t088p133-manuscript-r1/packet/public'
s=(old/'main.tex').read_text()
s=s.replace('T088P133 manuscript draft, round 1','T088P133 final-manuscript implementation, round 2')
a=s.index(r'\noindent\textit{Draft status.}');b=s.index('\n\\section',a)
s=s[:a]+r'''\noindent\textit{Review status.} The full proof and exact finite support are
presented for independent manuscript review. Independently reviewed Lean
support covers only the deterministic algebra of Proposition B; the full
geometric theorem is unformalized. This implementation confers no acceptance
or release. Original prose: CC BY 4.0; original code: MIT.
'''+s[b:]
needle='Under scaling $b\\mapsto\\lambda b$'
pos=s.index(needle)
note=r'''% BEGIN R2 FORMAL USE-SITE NOTE
\paragraph{Reviewed formal support at this use site.}
The unchanged algebra above is supported by
\path|T088P133.rational_mixture_lt_one|~\cite{formalimpl,formalreview},
with $q=1-p$, $A=P/p$, $B=N/q$ and the moments in \eqref{eq:Sn}.
The independent audit's \path|T088P133Review.original_normalized_slack|
checks exactly \eqref{eq:two-brackets};
\path|scalar_majorization_use| composes the strict bound with an
\emph{assumed scalar} inequality of the form \eqref{eq:mixture}.
It does not prove \eqref{eq:mixture} for an expectation.
The reduced $p=1$ and $p=0$ expressions are covered separately.
Appendix~\ref{app:formal} gives the precise hypotheses, declaration mapping
and trust boundary. The probability comparison, certificate and geometric
assembly remain the mathematical arguments in this paper.
% END R2 FORMAL USE-SITE NOTE

'''
s=s[:pos]+note+s[pos:]
a=s.index(r'\paragraph{Formal coverage and next immutable round.}');b=s.index(r'\paragraph{Rights and reproducibility.}',a)
s=s[:a]+r'''\paragraph{Formal integration history.}
The immutable round-1 manuscript truthfully recorded formal support as
pending at its time of drafting. The completed implementation and separate
independent scoped review are now authenticated and integrated here,
without changing either original package. The parent adopted
\texttt{PASS\_SCOPED\_SUPPORT}, with no repairs, for deterministic algebra
only. This is not a full mathematical, manuscript, acceptance, count or
release verdict. Appendix~\ref{app:formal} states its actual coverage.
The parent's earlier manuscript intake checked artifacts and sampled layout;
it was not an independent all-page manuscript review.

'''+s[b:]
s=s.replace('For this draft, Source P', 'For the round-1 draft, Source P')
s=s.replace('This draft read its opening statements', 'The round-1 draft read its opening statements')
s=s.replace('This is a local draft,\nnot a portable release or publication.', 'This is a local manuscript implementation for independent review,\nnot a release or publication.')
s=s.replace('\\input{references.tex}', '\\input{formal-appendix.tex}\n\n\\input{references.tex}')
(p/'main.tex').write_text(s)
bib=(old/'references.tex').read_text().replace('\\end{thebibliography}',r'''\bibitem{formalimpl}
M.~Kang, \emph{T088P133: Proposition B deterministic algebra, implementation
round 1}, October 20, 2026. Codex / GPT-6 Astra / high / default-tier provenance.
Unchanged Lean sources, pins, coverage and rebuild script retained in
\path|formal/implementation/|. Original code MIT; original prose CC BY 4.0.

\bibitem{formalreview}
M.~Kang, \emph{Independent scoped formal review, T088P133, round 1},
October 20, 2026. Codex / GPT-6.1-Sol / high / default-tier provenance.
Verdict \texttt{PASS\_SCOPED\_SUPPORT}, no required repairs; adopted by parent.
Unchanged semantic audit and review retained in \path|formal/review/|.
Local independent AI review, not human peer review or full-theorem formalization.
\end{thebibliography}''')
(p/'references.tex').write_text(bib)
