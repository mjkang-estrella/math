\LoadClass[12pt,oneside]{amsart}
\RequirePackage{amsmath,amssymb,latexsym, amsthm, amscd, mathrsfs, stmaryrd, mathtools}
\RequirePackage[linktocpage=true]{hyperref}
\RequirePackage{cleveref}
\RequirePackage{xcolor}
%\RequirePackage{epsfig} %importing graphic
\RequirePackage[all]{xy}
\RequirePackage{enumitem}
\RequirePackage{chngcntr}
\RequirePackage{multirow}
\RequirePackage{array}
\RequirePackage{booktabs}
\RequirePackage{tikz}
\RequirePackage[margin=1in]{geometry}

%\RequirePackage[sorting=nyt,hyperref=true,doi=false,maxbibnames=9,maxcitenames=4,url=false,isbn=false]{biblatex}
%\renewbibmacro{in:}{}
%\addbibresource{bib.bib}

\crefformat{section}{\S#2#1#3} % see manual of cleveref, section 8.2.1
\crefformat{subsection}{\S#2#1#3}
\crefformat{subsubsection}{\S#2#1#3}

%%%%%%%Page stuff%%%%%%%%%%%%%
\setlength{\hoffset}{0pt}
\setlength{\voffset}{0pt}
\setlength{\topmargin}{0pt}
\setlength{\oddsidemargin}{0in}
\setlength{\evensidemargin}{0in}
\setlength{\textheight}{8.75in}
\setlength{\textwidth}{6.5in}
% \AtBeginDocument{%
%  \abovedisplayskip=5pt plus 1pt minus 1pt
%  \abovedisplayshortskip=5pt plus 1pt
%  \belowdisplayskip=5pt plus 1pt minus 1pt
%  \belowdisplayshortskip=5pt plus 1pt minus 1pt
% }
\pagestyle{headings}
%\renewcommand{\baselinestretch}{1.25}


%%%%%%%%theorem stuff%%%%%%%%%
\newtheorem{theorem}{Theorem}[section]
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{conjecture}[theorem]{Conjecture}

\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}%[section]
\newtheorem{example}[theorem]{Example}%[section]
\newtheorem{question}[theorem]{Question}%[section]

\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}%[section]


\numberwithin{equation}{section}


%color
\newcommand{\blue}[1]{{\color{blue}#1}}
\newcommand{\red}[1]{{\color{red}#1}}
\newcommand{\green}[1]{{\color{green}#1}}

\newcommand{\comment}[1]{}