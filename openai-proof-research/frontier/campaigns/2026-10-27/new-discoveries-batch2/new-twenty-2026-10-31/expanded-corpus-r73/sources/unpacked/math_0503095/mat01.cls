\NeedsTeXFormat{LaTeX2e}[1995/12/01]
\ProvidesClass{mat01}
              [1998/09/01 v0.1
 Standard LaTeX document class for IAS-JAA Journals]
\newcommand\@ptsize{}
\newif\if@restonecol
\newif\if@titlepage
\@titlepagefalse
\newif\if@nameyear
\@nameyearfalse
%%% PAPER SIZE %% TRIM
\DeclareOption{a4paper}
   {\setlength\paperheight {297mm}%
    \setlength\paperwidth  {210mm}}
\DeclareOption{a5paper}
   {\setlength\paperheight {210mm}%
    \setlength\paperwidth  {148mm}}
\DeclareOption{b5paper}
   {\setlength\paperheight {250mm}%
    \setlength\paperwidth  {176mm}}
\DeclareOption{letterpaper}
   {\setlength\paperheight {11in}%
    \setlength\paperwidth  {8.5in}}
\DeclareOption{custom}
   {\setlength\paperheight {25cm}%
    \setlength\paperwidth  {17.5cm}}
\DeclareOption{legalpaper}
   {\setlength\paperheight {14in}%
    \setlength\paperwidth  {8.5in}}
\DeclareOption{executivepaper}
   {\setlength\paperheight {10.5in}%
    \setlength\paperwidth  {7.25in}}
\DeclareOption{landscape}
   {\setlength\@tempdima   {\paperheight}%
    \setlength\paperheight {\paperwidth}%
    \setlength\paperwidth  {\@tempdima}}
\DeclareOption{nameyear}{\@nameyeartrue}
%%%%  TYPE SIZE %%
\DeclareOption{10pt}{\renewcommand\@ptsize{0}}
\DeclareOption{11pt}{\renewcommand\@ptsize{1}}
\DeclareOption{12pt}{\renewcommand\@ptsize{2}}
\DeclareOption{oneside}{\@twosidefalse \@mparswitchfalse}
\DeclareOption{twoside}{\@twosidetrue  \@mparswitchtrue}
\DeclareOption{draft}{\setlength\overfullrule{5pt}}
\DeclareOption{final}{\setlength\overfullrule{0pt}}
\DeclareOption{titlepage}{\@titlepagetrue}
\DeclareOption{notitlepage}{\@titlepagefalse}
\DeclareOption{onecolumn}{\@twocolumnfalse}
\DeclareOption{twocolumn}{\@twocolumntrue}
%\DeclareOption{thms}{\PassOptionsToPackage{\CurrentOption}{klumath}}
%\DeclareOption{mathsec}{\PassOptionsToPackage{\CurrentOption}{klumath}}
%\DeclareOption{fleqn}{\PassOptionsToPackage{\CurrentOption}{klumath}}
%\DeclareOption{leqno}{\PassOptionsToPackage{\CurrentOption}{klumath}}
%\DeclareOption{leqno}{\input{leqno.clo}}
%\DeclareOption{fleqn}{\input{fleqn.clo}}

\let\if@openbib\iffalse
\DeclareOption{openbib}{\let\if@openbib\iftrue}


\ExecuteOptions{a4paper,twoside,onecolumn,fleqn,final}
\ProcessOptions
\renewcommand\normalsize{%
   \@setfontsize\normalsize{10pt}{12} %10.5 12.5
   \abovedisplayskip 10\p@ \@plus2\p@ \@minus5\p@
   \abovedisplayshortskip \z@ \@plus3\p@
   \belowdisplayshortskip 6\p@ \@plus3\p@ \@minus3\p@
   \belowdisplayskip \abovedisplayskip
   \let\@listi\@listI}
\normalsize
\newcommand\small{%
   \@setfontsize\small\@ixpt{11}%
   \abovedisplayskip 8.5\p@ \@plus3\p@ \@minus4\p@
   \abovedisplayshortskip \z@ \@plus2\p@
   \belowdisplayshortskip 4\p@ \@plus2\p@ \@minus2\p@
   \def\@listi{\leftmargin\leftmargini
               \topsep 4\p@ \@plus2\p@ \@minus2\p@
               \parsep 2\p@ \@plus\p@ \@minus\p@
               \itemsep \parsep}%
   \belowdisplayskip \abovedisplayskip
}
\newcommand\footnotesize{%
%   \@setfontsize\footnotesize{10}{12}%
   \@setfontsize\footnotesize{8}{10}%
   \abovedisplayskip 6\p@ \@plus2\p@ \@minus4\p@
   \abovedisplayshortskip \z@ \@plus\p@
   \belowdisplayshortskip 3\p@ \@plus\p@ \@minus2\p@
   \def\@listi{\leftmargin\leftmargini
               \topsep 3\p@ \@plus\p@ \@minus\p@
               \parsep 2\p@ \@plus\p@ \@minus\p@
               \itemsep \parsep}%
   \belowdisplayskip \abovedisplayskip
}
\newcommand\scriptsize{\@setfontsize\scriptsize\@ixpt\@ixpt}
\newcommand\tiny{\@setfontsize\tiny\@vpt\@vipt}
\newcommand\large{\@setfontsize\large{13.5}{15.5}}
\newcommand\erlar{\@setfontsize\erlar{13.5}{19}}
\newcommand\aut{\@setfontsize\aut{11}{13}}
\newcommand\vcj{\@setfontsize\vcj{12}{14}}
\newcommand\larg{\@setfontsize\larg{10.4}{12.4}}
%\newcommand\footnotesize{\@setfontsize\large{12}{14}}
\newcommand\Large{\@setfontsize\Large{16}{18}}
\newcommand\volc{\@setfontsize\volc{17}{19}}
%\newcommand\fpe{\@setfontsize\fpe{19}{21}}
\newcommand\fpe{\@setfontsize\fpe{18}{21}}
\newcommand\LARGE{\@setfontsize\LARGE\@xviipt{22}}
\newcommand\ke{\@setfontsize\ke{9.45}{10}}
\newcommand\kes{\@setfontsize\kes{8}{9.5}}
\newcommand\bis{\@setfontsize\bis{9.5}{11}}
\newcommand\ais{\@setfontsize\ais{8.5}{10}}
\newcommand\bas{\@setfontsize\bas{8.8}{10}}
\newcommand\abs{\@setfontsize\abs{9}{10}}
\newcommand\xxx{\@setfontsize\xxx{10}{12}}
\newcommand\xx{\@setfontsize\xx{18}{20}}
\newcommand\xy{\@setfontsize\xy{10}{12}}
\newcommand\xz{\@setfontsize\xz{8.5}{10}}
\newcommand\ab{\@setfontsize\ab{7}{8}}

\newcommand\huge{\@setfontsize\huge\@xxpt{25}}
\newcommand\Huge{\@setfontsize\Huge\@xxvpt{30}}
\setlength\parindent{1em}
\newdimen\@bls                             
\@bls=\baselineskip                        
\bigskipamount=\@bls \@plus 0.3\@bls \@minus 0.3\@bls
\medskipamount=0.5\bigskipamount                  
\smallskipamount=0.25\bigskipamount               
\setlength\headheight{6\p@}
\setlength\headsep   {18\p@}
\setlength\topskip   {6\p@}
%\setlength\footskip{30\p@}
\setlength\maxdepth{.5\topskip}
\setlength\oddsidemargin{18truemm}   
\setlength\evensidemargin{18truemm}
\setlength\marginparwidth{\z@}   
\setlength\marginparsep{3mm}      
\setlength\topmargin{17truemm}          
%%% TEXT AREA %%                          
\textheight 20.2cm
%\advance\textheight\topskip  
\textwidth 12.5cm
\columnsep 0.5cm
\columnseprule \z@           
\setlength\footnotesep{6.65\p@}
\setlength{\skip\footins}{9\p@ \@plus 4\p@ \@minus 2\p@}
\setlength\floatsep    {12\p@ \@plus 2\p@ \@minus 2\p@}
\setlength\textfloatsep{12\p@ \@plus 6\p@ \@minus 6\p@}
\setlength\intextsep   {12\p@ \@plus 6\p@ \@minus 6\p@}
\setlength\dblfloatsep    {12\p@ \@plus 6\p@ \@minus 6\p@}
\setlength\dbltextfloatsep{12\p@ \@plus 6\p@ \@minus 6\p@}
\setlength\@fptop{0\p@ \@plus 1fil}
\setlength\@fpsep{8\p@ \@plus 2fil}
\setlength\@fpbot{0\p@ \@plus 1fil}
\setlength\@dblfptop{0\p@ \@plus 1fil}
\setlength\@dblfpsep{8\p@ \@plus 2fil}
\setlength\@dblfpbot{0\p@ \@plus 1fil}
\setlength\partopsep{2\p@ \@plus 1\p@ \@minus 1\p@}
\setlength\lineskip{1\p@}
\setlength\normallineskip{1\p@}
\renewcommand\baselinestretch{}
\setlength\parskip{\z@}
\@lowpenalty   51
\@medpenalty  151
\@highpenalty 301
\@beginparpenalty -\@lowpenalty    % Before a list or paragraph environment.
\@endparpenalty   -\@lowpenalty    % After a list or paragraph environment.
\@itempenalty     -\@lowpenalty    % Between list items.
%%% FLOATS %%
\setcounter{topnumber}{5}
\def\topfraction{0.99}
\def\textfraction{0.05}
\def\floatpagefraction{0.9}
\setcounter{bottomnumber}{5}
\def\bottomfraction{0.99}
\setcounter{totalnumber}{10}
\def\dbltopfraction{0.99}
\def\dblfloatpagefraction{0.8}
\setcounter{dbltopnumber}{5}
%
\newcommand\contentsname{Contents}
\newcommand\listfigurename{List of Figures}
\newcommand\listtablename{List of Tables}
\newcommand\refname{References}
\newcommand\indexname{Index}
\newcommand\figurename{Figure}
\newcommand\tablename{Table}
\newcommand\partname{Part}
\newcommand\appendixname{Appendix}
\newcommand\abstractname{Abstract}
%\newcommand\abstractname{Summary}
\newbox\t@abstract
\newbox\temptbox
\newdimen\tempdime
%%% PAGE STYLE %%
%
\def\@journal{Proc. Indian Acad. Sci. (Math. Sci.)}
\def\@vol{xx}
\def\@pa{xx}
\def\@pmon{??}
\def\@pubyear{19??}
\def\@key{??}
%\def\journal#1{%
%\def\@tempa{#1}\def\@tempb{ejpp}\def\@tempc{neon}\def\@tempd{canc}
%\ifx\@tempb\@tempa\gdef\@journal{European Journal of Plant Pathology}\fi
%\ifx\@tempc\@tempa\gdef\@journal{Journal of Neuro-Oncology}\fi
%\ifx\@tempd\@tempa\gdef\@journal{Cancer and Metastasis Reviews}\fi}
\def\volume#1{\gdef\@vol{#1}}
\def\parts#1{\gdef\@pa{#1}}
\def\pubyear#1{\gdef\@pubyear{#1}}
%\def\keyword#1{\gdef\@key{{\bf Key~words.}~#1}}
\def\mon#1{\gdef\@pmon{#1}}

\font\df=sy at 9pt
\def\copyt{\mbox{\df\char'343}}

%\def\@key{{\it Key~words:}}
\newcounter{firstpage}
\newcounter{lastpage}
\def\firstpage#1{\def\@tempa{#1}\ifx\@tempa\@empty\else
  \setcounter{firstpage}{#1}%
  \global\c@page=#1 \ignorespaces\fi}
\setcounter{firstpage}{1}
\setcounter{lastpage}{0}
\def\lastpage#1{\def\@tempa{#1}\ifx\@tempa\@empty\else
  \setcounter{lastpage}{#1}\ignorespaces\fi}
\def\ps@openin{\let\@mkboth\@gobbletwo
 \def\@oddhead{{\vbox{\vskip-9pt\ais\noindent\hsize\textwidth{\@journal\/}\ 
\ {Vol. \@vol,}\ {No. \@pa,} \ {\@pmon} 2003, \ pp. \arabic{firstpage}--\arabic{lastpage}.\\ \copyright \ Printed in India\vfill}\hfil}}%\ (\@pubyear)\ 
 \def\@evenhead{}%
 \def\@oddfoot{
{\vbox{\vskip 1.35pc\normalsize\noindent\hsize\textwidth
\hfill \thepage}}



}%
 \let\@evenfoot\@oddfoot}
  \def\ps@headings{%
      \let\@oddfoot\@empty\let\@evenfoot\@empty
      \def\@evenhead{\normalsize\!\!\thepage\hskip 4pc{\it \leftmark}\hfil}%
      \def\@oddhead{\normalsize\hskip 4pc{\it \rightmark}\hfil\thepage}%
      \let\@mkboth\markboth
      }
\def\ps@myheadings{%
    \let\@oddfoot\@empty\let\@evenfoot\@empty
    \def\@evenhead{\thepage\hfil\slshape\leftmark}%
    \def\@oddhead{{\slshape\rightmark}\hfil\thepage}%
    \let\@mkboth\@gobbletwo
    \let\sectionmark\@gobble
    \let\subsectionmark\@gobble
    }
\newcommand\maketitle{\par
  \begingroup
    \renewcommand\thefootnote{\@fnsymbol\c@footnote}%
    \def\@makefnmark{\rlap{\@textsuperscript{\normalfont\@thefnmark}}}%
    \long\def\@makefntext##1{\parindent 1em\noindent
            \hb@xt@0.4em{%1.8
                \hss\@textsuperscript{\normalfont\@thefnmark}}##1}%
      \ifnum \col@number=\@ne
        \@maketitle
      \else
        \twocolumn[\@maketitle]%
      \fi
    \thispagestyle{openin}\@thanks
  \endgroup
  \setcounter{footnote}{0}%
  \global\let\@type\@empty\global\let\type\relax
  \global\let\@title\@empty\global\let\title\relax
  \global\let\@author\@empty\global\let\author\relax
  \global\let\@thanks\@empty\global\let\thanks\relax
  \global\let\@address\@empty\global\let\address\relax
  \global\let\@Date\@empty\global\let\Date\relax
  \global\let\@keyword\@empty\global\let\keyword\relax
  \global\let\@abstract\@empty\global\let\abstract\relax
  \global\let\@abbrev\@empty\global\let\abbrev\relax
  \global\let\maketitle\relax\global\let\@maketitle\relax
}
\def\@maketitle{%
  \newpage
  \null
  \vskip 2\p@%
  \begin{flushleft}%
  \let \footnote \thanks
%    \vskip 1\p@%12
    \ifx\@type\undefined\vskip19\p@
	\else{\normalsize\it \@type \par}\vskip 7\p@%
	\fi%
\vskip .0pc
	   {\large\bf \@title \par}%
    \vskip 1.4\@bls%
    {\aut\quote\@author\ \par }%
    %\vskip \z@%
    \vskip 1pc			%%this need to be changed for address to come on next line
    {\quote\abs \@address \par}%
    \vskip 11\p@%
   \vskip 3.4\p@%
    \ifx\@Date	\undefined\else{\quote\abs \@Date \par}\vskip 9\p@%
    \fi%
    \vskip 3.4\p@%
    { \unvbox\t@abstract}%
    \vskip .9\@bls%
  {\abs\quote\@keyword \par}%
   % \ifx\@abbrev\undefined\else{\normalsize \@abbrev \par}\fi%
  \end{flushleft}}%
  %\par
%  \vskip 1\@bls
%%
\def\type#1{\def\@type{#1}}
\def\address#1{\def\@address{#1}}
\def\Date#1{\def\@Date{#1}}
\def\keyword#1{\def\@keyword{{\bf Keywords.}~~~~~#1}}
\def\abstract{\@ifnextchar[{\@abstract}{\@abstract[]}}
\def\abbrev#1{\def\@abbrev{{\it Abbreviations:}~#1}}
\def\@abstract[#1]{%
  \global\setbox\t@abstract=\vbox\bgroup
   \hsize 11.65cm
   \abs
  \parindent 1em                      
  \quote {\bfseries\abstractname.\ \ \ }  
  \noindent\ignorespaces}
 \def\endabstract{\par\egroup}

%%
%%
\setcounter{secnumdepth}{3}
\newcounter {part}
\newcounter {section}
\newcounter{ssection}
\newcounter {subsection}[section]
\newcounter {subsubsection}[subsection]
\newcounter {paragraph}[subsubsection]
\newcounter {subparagraph}[paragraph]
\renewcommand\thepart         {\@Roman\c@part}
\renewcommand\thesection      {\@arabic\c@section.}
\renewcommand\thessection      {\@arabic\c@section}
\renewcommand\thesubsection   {\thesection\@arabic\c@subsection}
\renewcommand\thesubsubsection{\thesubsection.\@arabic\c@subsubsection}
\renewcommand\theparagraph    {\thesubsubsection\@arabic\c@paragraph}
\renewcommand\thesubparagraph {\theparagraph\@arabic\c@subparagraph}
%%
\newcommand\part{\par
   \addvspace{4ex}%
   \@afterindentfalse
   \secdef\@part\@spart}
%%
\def\@part[#1]#2{%
    \ifnum \c@secnumdepth >\m@ne
      \refstepcounter{part}%
      \addcontentsline{toc}{part}{\thepart\hspace{1em}#1}%
    \else
      \addcontentsline{toc}{part}{#1}%
    \fi
    {\parindent \z@ \raggedright
     \interlinepenalty \@M
     \normalfont
     \ifnum \c@secnumdepth >\m@ne
       \Large\bfseries \partname~\thepart
       \par\nobreak
     \fi
     \huge \bfseries #2%
     \markboth{}{}\par}%
    \nobreak
    \vskip 3ex
    \@afterheading}
\def\@spart#1{%
    {\parindent \z@ \raggedright
     \interlinepenalty \@M
     \normalfont
     \huge \bfseries #1\par}%
     \nobreak
     \vskip 3ex
     \@afterheading}
%%
\def\@sect#1#2#3#4#5#6[#7]#8{\ifnum #2>\c@secnumdepth
     \let\@svsec\@empty\else
     \refstepcounter{#1}\edef\@svsec{\csname the#1\endcsname\hskip 0.5em}\fi
     \@tempskipa #5\relax
      \ifdim \@tempskipa>\z@
        \begingroup #6\relax
          \@hangfrom{\hskip #3\relax\@svsec}{\interlinepenalty \@M #8\par}%
        \endgroup
       \csname #1mark\endcsname{#7}\addcontentsline
         {toc}{#1}{\ifnum #2>\c@secnumdepth \else
                      \protect\numberline{\csname the#1\endcsname}\fi
                    #7}\else
        \def\@svsechd{#6\hskip #3\relax  %% \relax added 2 May 90
                   \@svsec #8\csname #1mark\endcsname
                      {#7}\addcontentsline
                           {toc}{#1}{\ifnum #2>\c@secnumdepth \else
                             \protect\numberline{\csname the#1\endcsname}\fi
                       #7}}\fi
     \@xsect{#5}}
%%
\newcommand\section{%
\@startsection {section}{1}{\z@}%
{-2\@bls \@plus -1\@bls \@minus -1\@bls}%
{.57\@bls}%
{\normalfont\larg\bfseries}}
\newcommand\subsection{%
\@startsection{subsection}{2}{\z@}%
{-1.1\@bls \@plus -1\@bls \@minus -0.5\@bls}%
{1\@bls}%
{\normalfont\normalsize\rm}}
\newcommand\subsubsection{%
\@startsection{subsubsection}{3}{\z@}%
{1em}%-1\@bls \@plus -1\@bls \@minus -0.5\@bls
{-1em}%
{\normalfont\normalsize\rm}}
\newcommand\paragraph{%
\@startsection{paragraph}{4}{\z@}%
{2.25ex \@plus1ex \@minus.2ex}%
{-.5em}%
{\normalfont\normalsize\itshape}}
%{\normalfont\normalsize\bfseries}}
\newcommand\subparagraph{%
\@startsection{subparagraph}{5}{\parindent}%
{3.25ex \@plus1ex \@minus .2ex}%
{-1em}%
{\normalfont\normalsize\bfseries}}
%%% LISTS %%
\newdimen\labelwidthi
\newdimen\labelwidthii
\newdimen\labelwidthiii
\newdimen\labelwidthiv
\def\normal@labelsep{0.5em}
\labelsep\normal@labelsep
\settowidth{\labelwidthi}{(iii)}
\settowidth{\labelwidthii}{(d)}
\settowidth{\labelwidthiii}{(iii)}
\settowidth{\labelwidthiv}{(M)}
\leftmargini\labelwidthi    \advance\leftmargini\labelsep
\leftmarginii\labelwidthii  \advance\leftmarginii\labelsep
\leftmarginiii\labelwidthiii \advance\leftmarginiii\labelsep
\leftmarginiv\labelwidthiv  \advance\leftmarginiv\labelsep
\def\setleftmargin#1#2{\settowidth{\@tempdima}{#2}\labelsep\normal@labelsep
  \csname labelwidth#1\endcsname\@tempdima
  \@tempdimb\@tempdima \advance\@tempdimb\labelsep
  \csname leftmargin#1\endcsname\@tempdimb}
\def\@listI{\leftmargin\leftmargini
  \labelwidth\labelwidthi \labelsep\normal@labelsep
  \topsep \z@ \partopsep\z@ \parsep\z@ \itemsep\z@
  \listparindent 1em}
\def\@listii{\leftmargin\leftmarginii
  \labelwidth\labelwidthii \labelsep\normal@labelsep
  \topsep\z@ \partopsep\z@ \parsep\z@ \itemsep\z@
  \listparindent 1em}
\def\@listiii{\leftmargin\leftmarginiii
  \labelwidth\labelwidthiii \labelsep\normal@labelsep
  \topsep\z@ \partopsep\z@ \parsep\z@ \itemsep\z@
  \listparindent 1em}
\def\@listiv{\leftmargin\leftmarginiv
  \labelwidth\labelwidthiv \labelsep\normal@labelsep
  \topsep\z@ \partopsep\z@ \parsep\z@ \itemsep\z@
  \listparindent 1em}
\let\@listi\@listI
\@listi
\def\left@label#1{{#1}\hss}
\def\right@label#1{\hss\llap{#1}}
\def\thick@label#1{\hspace\labelsep #1}
\newcount\@maxlistdepth
\@maxlistdepth=4
%
\setlength  \labelsep  {.5em}
\setlength  \labelwidth{\leftmargini}
\addtolength\labelwidth{-\labelsep}
\@beginparpenalty -\@lowpenalty
\@endparpenalty   -\@lowpenalty
\@itempenalty     -\@lowpenalty
\def\labelitemi{$\bullet$}          \def\labelitemii{$\cdot$}
\def\labelenumi{(\theenumi)}        \def\theenumi{\arabic{enumi}}
\def\labelenumii{(\alph{enumii})}   \def\theenumii{\theenumi\alph{enumii}}
\def\labelenumiii{(\roman{enumiii})}\def\theenumiii{\theenumii.\roman{enumiii}}
\def\labelenumiv{(\Alph{enumiv})}   \def\theenumiv{\theenumiii.\Alph{enumiv}}
\def\enumerate{\vskip 6pt%
  \ifnum \@enumdepth >\@maxlistdepth
    \@toodeep
  \else
    \advance\@enumdepth \@ne
    \edef\@enumctr{enum\romannumeral\the\@enumdepth}%
    \list{\csname label\@enumctr\endcsname}%
       {\usecounter{\@enumctr}
	\leftmargin15pt %20pt
       \let\makelabel=\right@label}
  \fi}
\def\enumerates{\vskip 6pt%
  \ifnum \@enumdepth >\@maxlistdepth
    \@toodeep
  \else
    \advance\@enumdepth \@ne
    \edef\@enumctr{enum\romannumeral\the\@enumdepth}%
    \list{\csname label\@enumctr\endcsname}%
       {\usecounter{\@enumctr}
	\leftmargin18pt
       \let\makelabel=\right@label}
  \fi}
\def\itemize{%
  \ifnum \@itemdepth >\@maxlistdepth
    \@toodeep
  \else
    \advance\@itemdepth \@ne
    \edef\@itemitem{labelitem\romannumeral\the\@itemdepth}%
     \setleftmargin{i}{--}%
     \setleftmargin{ii}{$\cdot$}%
    \list{\csname\@itemitem\endcsname}%
       {\let\makelabel\right@label}
  \fi}
\newcommand\es{\endlist\vskip 6.5pt}
\let\endenumerate\es
\let\endenumerates\es
\def\verse{\let\\=\@centercr
  \list{}{\itemsep\z@
  \itemindent \z@
  \listparindent\z@
  \rightmargin 1em
  \leftmargin \rightmargin}\item[]}
\let\endverse\endlist
\def\quotation{\list{}{\vskip 8pt\itemindent\z@
 \leftmargin 1em \rightmargin \z@
  \parsep \z@ \@plus 1pt}\item[]}
\newcommand\e{\endlist\vskip 8pt}
\let\endquotation\e
\def\quote{\list{}{\itemindent\z@
   \leftmargin 1.5cm }%
\item[]}
\let\endquote\endlist
\def\descriptionlabel#1{\hspace\labelsep \itshape #1}
\def\description{\list{}{\labelwidth\z@
  \leftmargin \z@ \itemindent \z@ %-\leftmargin
  \let\makelabel\descriptionlabel}}
\let\enddescription\endlist
%% APPENDIX
\newcommand\appendix{\par
  \setcounter{section}{0}%
  \setcounter{subsection}{0}%
  \renewcommand\thesection{\@Alph\c@section}}
%
\setlength\arraycolsep{5\p@}
\setlength\tabcolsep{6\p@}
\setlength\arrayrulewidth{.4\p@}
\setlength\doublerulesep{2\p@}
\setlength\tabbingsep{\labelsep}
%
\skip\@mpfootins = \skip\footins
\setlength\fboxsep{3\p@}
\setlength\fboxrule{.4\p@}
%
%\renewcommand\theequation{\@arabic\c@equation}
%\RequirePackage{klumath}[1998/02/11]
%
\newcounter{figure}
\renewcommand\thefigure{\@arabic\c@figure}
\def\fps@figure{tbp}
\def\ftype@figure{1}
\def\ext@figure{lof}
\def\fnum@figure{\figurename~\thefigure}
\newenvironment{figure}
               {\let\@makecaption\@makefigurecaption\@float{figure}}
               {\end@float}
\newenvironment{fig}
               {\let\@makecaption\@makefigcaption\@float{figure}}
               {\end@float}
\newenvironment{figure*}
               {\let\@makecaption\@makefigurecaption\@dblfloat{figure}}
               {\end@dblfloat}
\newenvironment{fig*}
               {\let\@makecaption\@makefigcaption\@dblfloat{figure}}
               {\end@dblfloat}

\newcounter{table}
\renewcommand\thetable{\@arabic\c@table}
\def\fps@table{tbp}
\def\ftype@table{2}
\def\ext@table{lot}
\def\fnum@table{\tablename~\thetable}
\newenvironment{table}
               {\let\@makecaption\@maketablecaption\@float{table}}
               {\end@float}
\newenvironment{table*}
               {\let\@makecaption\@maketablecaption\@dblfloat{table}}
               {\end@dblfloat}
\newlength\abovecaptionskip
\newlength\belowcaptionskip
\setlength\abovecaptionskip{6\p@}
\setlength\belowcaptionskip{6\p@}
%\long\def\@makecaption#1#2{%
%  \vskip\abovecaptionskip
%  \sbox\@tempboxa{#1.~#2}%
%  \ifdim \wd\@tempboxa >\hsize
%   #1.~#2\par
%  \else
%    \global \@minipagefalse
%    \hb@xt@\hsize{\hfil\box\@tempboxa\hfil}%
%  \fi
%  \vskip\belowcaptionskip}

%\long\def\@makefigurecaption#1#2{%
%  \vskip 7.75\p@%\abovecaptionskip
%    \normalsize {\it #1}.\enskip #2\par
%  }

\long\def\@makefigurecaption#1#2{\ke
        \vskip 12pt
	\setbox\@tempboxa\hbox{\hangindent=4pc\hangafter=0{{\bf #1.} \  \rm #2}} %\centerline
        \ifdim \wd\@tempboxa >\hsize 
                \par\unhbox\@tempboxa%
                \else
		\hbox to\hsize {\box\@tempboxa\hfil} 
        \fi}


\long\def\@makefigcaption#1#2{\ke
        \vskip 12pt
	\setbox\@tempboxa\hbox{{\hskip 4pc{\bf #1.} \ \rm #2}} %
        \ifdim \wd\@tempboxa >\hsize 
                \par\unhbox\@tempboxa%
                \else
		\hbox to\hsize {\box\@tempboxa\hfil} 
        \fi}


\long\def\@maketablecaption#1#2{\ke
        \setbox\@tempboxa\hbox{{\raggedright{\bf #1.}\ \hskip3.2pt \raggedright{#2}.}}
        \ifdim \wd\@tempboxa>\hsize \unhbox\@tempboxa%
                \else
                \hbox to\hsize{\box\@tempboxa\hfil}
        \fi\vskip 6pt}


%\long\def\@maketablecaption#1#2{%
%  \vskip 3\p@
%    \footnotesize {\it #1}.\enskip #2\par
%  \vskip\belowcaptionskip}

\DeclareOldFontCommand{\rm}{\normalfont\rmfamily}{\mathrm}
\DeclareOldFontCommand{\sf}{\normalfont\sffamily}{\mathsf}
\DeclareOldFontCommand{\tt}{\normalfont\ttfamily}{\mathtt}
\DeclareOldFontCommand{\bf}{\normalfont\bfseries}{\mathbf}
\DeclareOldFontCommand{\it}{\normalfont\itshape}{\mathit}
\DeclareOldFontCommand{\sl}{\normalfont\slshape}{\@nomath\sl}
\DeclareOldFontCommand{\sc}{\normalfont\scshape}{\@nomath\sc}
\DeclareRobustCommand*\cal{\@fontswitch\relax\mathcal}
\DeclareRobustCommand*\mit{\@fontswitch\relax\mathnormal}
%
\newcommand\@pnumwidth{1.55em}
\newcommand\@tocrmarg{2.55em}
\newcommand\@dotsep{4.5}
\setcounter{tocdepth}{3}
\newcommand\tableofcontents{%
    \section*{\contentsname
        \@mkboth{%
           \MakeUppercase\contentsname}{\MakeUppercase\contentsname}}%
    \@starttoc{toc}%
    }
\newcommand*\l@part[2]{%
  \ifnum \c@tocdepth >-2\relax
    \addpenalty\@secpenalty
    \addvspace{2.25em \@plus\p@}%
    \begingroup
      \setlength\@tempdima{3em}%
      \parindent \z@ \rightskip \@pnumwidth
      \parfillskip -\@pnumwidth
      {\leavevmode
       \large \bfseries #1\hfil \hb@xt@\@pnumwidth{\hss #2}}\par
       \nobreak
       \if@compatibility
         \global\@nobreaktrue
         \everypar{\global\@nobreakfalse\everypar{}}%
      \fi
    \endgroup
  \fi}
\newcommand*\l@section[2]{%
  \ifnum \c@tocdepth >\z@
    \addpenalty\@secpenalty
    \addvspace{1.0em \@plus\p@}%
    \setlength\@tempdima{1.5em}%
    \begingroup
      \parindent \z@ \rightskip \@pnumwidth
      \parfillskip -\@pnumwidth
      \leavevmode \bfseries
      \advance\leftskip\@tempdima
      \hskip -\leftskip
      #1\nobreak\hfil \nobreak\hb@xt@\@pnumwidth{\hss #2}\par
    \endgroup
  \fi}
\newcommand*\l@subsection{\@dottedtocline{2}{1.5em}{2.3em}}
\newcommand*\l@subsubsection{\@dottedtocline{3}{3.8em}{3.2em}}
\newcommand*\l@paragraph{\@dottedtocline{4}{7.0em}{4.1em}}
\newcommand*\l@subparagraph{\@dottedtocline{5}{10em}{5em}}
\newcommand\listoffigures{%
    \section*{\listfigurename
      \@mkboth{\MakeUppercase\listfigurename}%
              {\MakeUppercase\listfigurename}}%
    \@starttoc{lof}%
    }
\newcommand*\l@figure{\@dottedtocline{1}{1.5em}{2.3em}}
\newcommand\listoftables{%
    \section*{\listtablename
      \@mkboth{%
          \MakeUppercase\listtablename}{\MakeUppercase\listtablename}}%
    \@starttoc{lot}%
    }
\let\l@table\l@figure
%
\def\thebibliography{%
%\@startsection {section}{1}{\z@}%
%{-2\@bls \@plus -1\@bls \@minus -1\@bls}%
%{14\p@}{\normalfont\normalsize\bfseries}*{\refname}%
\section*{\refname} 
 \addcontentsline{toc}{section}{\refname}%
  \@thebibliography}
\let\endthebibliography=\endlist


\def\@thebibliography#1{\bis
  \list{\@biblabel{\@arabic\c@enumiv}} {\settowidth\labelwidth{\@biblabel{#1}} %\@biblabel{\arabic{enumiv}} %
  \if@nameyear
    \leftmargin\labelwidth \z@ \labelsep \z@ \leftmargin \parindent
    \itemindent \parindent 
  \else
    \labelsep .6pc \itemindent 0pt %\z@
    \leftmargin\labelwidth \advance\leftmargin\labelsep
  \fi
    %\itemsep 2\p@
    \usecounter{enumiv}\let\p@enumiv\@empty
    \def\theenumiv{\arabic{enumiv}}}%
  }
\if@nameyear
  \def\@biblabel#1{}
\else
%  \def\@biblabel#1{\hskip \z@ \@plus 1filll[#1]}
  \def\@biblabel#1{\hskip \z@ \@plus 1filll [#1]}
\fi




\newcount\@tempcntc
\def\@citex[#1]#2{\if@filesw\immediate\write\@auxout{\string\citation{#2}}\fi
 \@tempcnta\z@\@tempcntb\m@ne\def\@citea{}\@cite{\@for\@citeb:=#2\do
  {\@ifundefined
   {b@\@citeb}{\@citeo\@tempcntb\m@ne\@citea\def\@citea{,}{\bfseries ?}\@warning
   {Citation `\@citeb' on page \thepage \space undefined}}%
  {\setbox\z@\hbox{\global\@tempcntc0\csname b@\@citeb\endcsname\relax}%
   \ifnum\@tempcntc=\z@ \@citeo\@tempcntb\m@ne
    \@citea\def\@citea{,}\hbox{\csname b@\@citeb\endcsname}%
   \else
    \advance\@tempcntb\@ne
    \ifnum\@tempcntb=\@tempcntc
    \else\advance\@tempcntb\m@ne\@citeo
    \@tempcnta\@tempcntc\@tempcntb\@tempcntc\fi\fi}}\@citeo}{#1}}
\def\@citeo{\ifnum\@tempcnta>\@tempcntb\else\@citea\def\@citea{,}%
 \ifnum\@tempcnta=\@tempcntb\the\@tempcnta\else
  {\advance\@tempcnta\@ne\ifnum\@tempcnta=\@tempcntb \else \def\@citea{--}\fi
   \advance\@tempcnta\m@ne\the\@tempcnta\@citea\the\@tempcntb}\fi\fi}
\newenvironment{theindex}
               {\if@twocolumn
                  \@restonecolfalse
                \else
                  \@restonecoltrue
                \fi
                \columnseprule \z@
                \columnsep 35\p@
                \twocolumn[\section*{\indexname}]%
                \@mkboth{\MakeUppercase\indexname}%
                        {\MakeUppercase\indexname}%
                \thispagestyle{plain}\parindent\z@
                \parskip\z@ \@plus .3\p@\relax
                \let\item\@idxitem}
               {\if@restonecol\onecolumn\else\clearpage\fi}
\newcommand\@idxitem{\par\hangindent 40\p@}
\newcommand\subitem{\@idxitem \hspace*{20\p@}}
\newcommand\subsubitem{\@idxitem \hspace*{30\p@}}
\newcommand\indexspace{\par \vskip 10\p@ \@plus5\p@ \@minus3\p@\relax}
\renewcommand\footnoterule{%
  \kern-3\p@
  \hrule\@width20truemm
  \kern2.6\p@}
\newcommand\@makefntext[1]{%
    \parindent 0em%
    \noindent
    \hb@xt@0.5em{\hss\@makefnmark}#1}  %1.8em
\newcommand\today{}
\edef\today{\ifcase\month\or
  January\or February\or March\or April\or May\or June\or
  July\or August\or September\or October\or November\or December\fi
  \space\number\day, \number\year}
\def\enddocument{\@checkend{document}\clearpage%
\addtocounter{page}{-1}%
\immediate\write\@auxout{%
\string\global\string\c@lastpage=\the\c@page}
\addtocounter{page}{1}%
\begingroup
\if@filesw \immediate\closeout\@mainaux
\def\newlabel{\@testdef r}%
\def\bibcite{\@testdef b}\@tempswafalse \makeatletter\input \jobname.aux
\if@tempswa \@@warning{Label(s) may have changed.  Rerun to get
cross-references right}\fi\fi\endgroup\deadcycles\z@\@@end}
%
\def\copyright{\mbox{\rm\char'251}}
%
\newenvironment{processtable}[3]{\setbox\temptbox=\hbox{{\ke #2}}%
\tempdime\wd\temptbox\@processtable{#1}{#2}{#3}{\tempdime}}
{\relax}
\newenvironment{@processtable}[4]{\begin{center}\begin{minipage}[t]{#4}%
\caption{#1}{\ke #2}\vskip4pt\tabnote{#3}\end{minipage}
\end{center}}{\relax}
\newenvironment{tabnote}[1]{\par\noindent\footnotesize #1}{\par}
%
\def\artpath#1{\def\@artpath{#1}}
\newenvironment{processfigure}[5]{%
\begin{center}
\begin{minipage}[t]{\hsize}
\showtiff{#1}{#2}{#3}{#4}
\caption{#5}
\end{minipage}
\end{center}}
{\par}
%
% Arguments to showtiff are: file-name, desired width, columns, rows.
% The height is computed from the widths so as to preserve the aspect ratio.
% The number of rows and columns is *only* used to compute height from width.
% The number of columns and rows in the TIFF image may be found using TIFFTAGS.
% TeX cannot read the binary TIFF file to extract the dimensions for itself.
\newdimen\dwidth
\newdimen\dheight
\newcount\ncolumns
\newcount\nrows
\def\showtiff#1#2#3#4{
\dwidth=#2\dheight=#2
\ncolumns=#3\nrows=#4
\divide\dheight by \ncolumns
\multiply\dheight by \nrows
\edef\width{\number\dwidth}
\edef\height{\number\dheight}
\centerline{\vbox to \dheight{\vfill\hbox to \dwidth{
\special{insertimage: \@artpath/#1 \width \space \height}\hfill}}}}
% The above assumes that the X and Y resolution are the same
% If they are not, then change the aspect ratio to suit
% Make <height> = <true height> * <x resolution> / <y resolution>
% Use TIFFTAGS to find the x and y resolution (if specified)
\newif\ifcropmarkson
\def\printcropmarks{\global\cropmarksontrue}
\newdimen\widthofcropmarks
\widthofcropmarks=19.5cm
\newdimen\raisetopcropmarks
\raisetopcropmarks=-34\p@
\newdimen\raisebottomcropmarks
\raisebottomcropmarks-2cm
\newdimen\movecropmarksright
\movecropmarksright\z@
\def\topcropmarks{\ifcropmarkson
\vtop to0pt{\vss
\hbox to0pt{\hskip\movecropmarksright\hbox to0pt{\hss%
\hbox to2pc{\hrulefill\hskip3pt}\raise6pt\hbox{\vrule height 2pc}}%
\hskip\widthofcropmarks%
\hbox to0pt{%
\raise6pt\hbox{\vrule height 2pc}\hbox to2pc{\hskip3pt\hrulefill}\hss}\hss}%
\vskip\raisetopcropmarks}
\fi}
%
\def\mscode#1{\gdef\@code{CANC~#1}}
\def\prodelem#1{\gdef\@element{PIPS #1}}
\def\arttype#1{\gdef\@typey{#1}}
\mscode{????}
\prodelem{????}
\arttype{????}


\newenvironment{processtab}[3]{\setbox\temptbox=\hbox{{#2}}%
\tempdime\wd\temptbox\@processtab{#1}{#2}{#3}{\tempdime}}
{\relax}
\newenvironment{@processtab}[4]{\begin{center}\begin{minipage}[t]{#4}%
\caption{#1}{#2}\vskip4pt\tabnote{#3}\end{minipage}
\end{center}}{\relax}
%
% TABLE
\renewenvironment{processtab}[3]{\setbox\temptbox=\hbox{{#2}}%
\tempdime\wd\temptbox\@processtab{#1}{#2}{#3}{\tempdime}}
{\relax}
\renewenvironment{@processtab}[4]{%
\if@kaprotate
\setbox4=\hbox to \textheight{\vbox{\hsize\textheight\begin{center}\begin{minipage}[c]{#4}%
{\ke #2}\vskip2pt\tabnote{#3}\end{minipage}
\end{center}}}
\else
\setbox4=\hbox to \hsize{\vbox{\begin{center}\begin{minipage}[t]{#4}%
{\ke #2}\vskip4pt\tabnote{#3}\end{minipage}
\end{center}}}
\fi
\if@kaprotate\rotl{4}\else\box4\fi
}
{\relax}



\def\bottomcropmarks{\ifcropmarkson
\vtop to0pt{\vskip-\raisebottomcropmarks
\hbox to0pt{\hskip\movecropmarksright\hbox to0pt{\hss%
\hbox to2pc{\hrulefill\hskip3pt}\lower6pt\hbox{\vrule depth 2pc height 0pt}}%
%\hskip\widthofcropmarks%
\hbox to \widthofcropmarks{\hfill \vbox to 0pt{\vskip6pt\ifnum\value{page}=\value{firstpage}{\hbox{\sf \@typey\qquad \@code\qquad\@element}}\fi}\hfill}
\hbox to0pt{%
\lower6pt\hbox{\vrule depth 2pc height0pt}\hbox to2pc{\hskip3pt\hrulefill}\hss}\hss}%
\vss}\fi}
\def\@outputpage{%
\begingroup           % the \endgroup is put in by \aftergroup
  \let \protect \noexpand
  \@resetactivechars
  \let\-\@dischyph
  \let\'\@acci\let\`\@accii\let\=\@acciii
  \let\\\@normalcr
  \let\par\@@par          %% 15 Sep 87
  \shipout \vbox{\topcropmarks%
    \set@typeset@protect
    \aftergroup \endgroup
    \aftergroup \set@typeset@protect
  \if@specialpage
    \global\@specialpagefalse\@nameuse{ps@\@specialstyle}%
  \fi
  \if@twoside
    \ifodd\count\z@ \let\@thehead\@oddhead \let\@thefoot\@oddfoot
         \let\@themargin\oddsidemargin
    \else \let\@thehead\@evenhead
       \let\@thefoot\@evenfoot \let\@themargin\evensidemargin
    \fi
  \fi
  \reset@font 
  \normalsize
  \baselineskip\z@skip \lineskip\z@skip \lineskiplimit\z@
    \@begindvi
    \vskip \topmargin
    \moveright\@themargin \vbox {%
      \setbox\@tempboxa \vbox to\headheight{%
        \vfil
        \color@hbox
          \normalcolor
          \hb@xt@\textwidth {%
            \let \label \@gobble
            \let \index \@gobble
            \let \glossary \@gobble %% 21 Jun 91
            \@thehead
            }%
        \color@endbox
        }%                        %% 22 Feb 87
      \dp\@tempboxa \z@
      \box\@tempboxa
      \vskip \headsep
      \box\@outputbox
      \baselineskip \footskip
      \color@hbox
        \normalcolor
        \hb@xt@\textwidth{%
          \let \label \@gobble
          \let \index \@gobble      %% 22 Feb 87
          \let \glossary \@gobble   %% 21 Jun 91
          \@thefoot
          }%
      \color@endbox
      }%
    \bottomcropmarks}%
\global \@colht \textheight
\stepcounter{page}%
\let\firstmark\botmark
}
%%%% FLOAT MECHANISM CHANGED 17 SEPT 1998
\newif\if@kaprotate \@kaprotatefalse
\def\kaprotate{\global\@kaprotatetrue}
\def\endkaprotate{\global\@kaprotatefalse}
\newdimen\rotdimen
\def\rotstart#1{\special{ps: gsave currentpoint currentpoint translate
    #1 neg exch neg exch translate}}
\def\rotfinish{\special{ps: currentpoint grestore moveto}}
\def\rotl#1{\rotdimen=\ht#1\advance\rotdimen by \dp#1
    \hbox to \rotdimen{\vbox to\wd#1{\vskip \wd#1
    \rotstart{270 rotate}\box #1\vss}\hss}\rotfinish}
\def\rotr#1{\rotdimen=\ht #1\advance\rotdimen by \dp#1
    \hbox to \rotdimen{\vbox to \wd#1{\vskip \wd#1
    \rotstart{90 rotate}\box #1\vss}\hss}\rotfinish}
% FIGURE
\renewenvironment{processfigure}[5]{%
\if@kaprotate
\setbox4=\hbox to \textheight{\vbox{\hsize\textheight\begin{center}
\begin{minipage}[t]{\textheight}
\showtiff{#1}{#2}{#3}{#4}
\caption{#5}
\end{minipage}
\end{center}}}
\else
\setbox4=\hbox to \hsize{\vbox{\begin{center}
\begin{minipage}[t]{\hsize}
\showtiff{#1}{#2}{#3}{#4}
\caption{#5}
\end{minipage}
\end{center}}}
\fi
\if@kaprotate\rotl{4}\else\box4\fi
}
{\par}
% TABLE
\renewenvironment{processtable}[3]{\setbox\temptbox=\hbox{{\ke #2}}%
\tempdime\wd\temptbox\@processtable{#1}{\ke #2}{#3}{\tempdime}}
{\relax}
\renewenvironment{@processtable}[4]{%
\if@kaprotate
\setbox4=\hbox to \textheight{\vbox{\hsize\textheight\begin{center}\begin{minipage}[c]{#4}%
\caption{#1}{\ke #2}\vskip4pt\tabnote{\ke #3}\end{minipage}
\end{center}}}
\else
\setbox4=\hbox to \hsize{\vbox{\begin{center}\begin{minipage}[t]{#4}%
\caption{#1}{\ke #2}\vskip4pt\tabnote{\ke #3}\end{minipage}
\end{center}}}
\fi
\if@kaprotate\rotl{4}\else\box4\fi
}
{\relax}
%%%%%

%\printcropmarks
%\font\test=eurm10 at 10pt %for roman mu
%\font\testa=eurm10 at 8pt %for roman mu
%\font\testb=eurm10 at 6pt %for roman mu
%\def\rmu{\mathchoice{\mbox{\test \char'26}}{\mbox{\test \char'26}}{\mbox{\testa \char'26}}{\mbox{\testb \char'26}}}
%\def\rmuf{\mbox{\testa \char'26}}

\def\rmu{\rm \char'265}
\def\trade{\rm \char'231}

\pagestyle{headings}
\pagenumbering{arabic}
%\twocolumn\sloppy
\frenchspacing
\flushbottom
%%% special parameters for TeX
\adjdemerits=100
\linepenalty=100
\doublehyphendemerits=10000 
\lefthyphenmin=3
\righthyphenmin=3       
\emergencystretch=1.6pc
\voffset-.65in
\hoffset-0.7in

\input amsmath.sty

\def\@mathmargin{1.7cm}



\topsep10\p@ \@plus2\p@ \@minus5\p@

\def\endmark{\hfill$\Box$\par}
\def\proof{\trivlist \item[\hskip \labelsep{\it Proof.}]}
\def\endproof{\null\hfill\endtrivlist}

%%%%%theorems

\def\theoremfont{\ifx\@currenvir\ex@mple
        \def\@thmfont{\rm} \else
        \ifx\@currenvir\ex@rcise
        \def\@thmfont{\rm} \else
        \ifx\@currenvir\d@finition
        \def\@thmfont{\rm} \else
        \ifx\@currenvir\rem@rk
        \def\@thmfont{\rm} \else
        \ifx\@currenvir\ass@mptions
        \def\@thmfont{\rm} \else
        \ifx\@currenvir\con@truction
        \def\@thmfont{\rm} \else
        \def\@thmfont{\it}\fi\fi\fi\fi\fi\fi}
\@addtoreset{definition}{section}
\@addtoreset{defin}{subsection}
\@addtoreset{defin1}{subsubsection}
\newtheorem{defin}{}[ssection]
\newtheorem{defin1}{}[subsubsection]
\newtheorem{definition}{Definition}[subsection]
\newtheorem{Definition}[defin]{Definition}
%\newtheorem{proof}[definition]{Proof}
\newtheorem{theorem}[defin]{\bf Theorem}
\newtheorem{Theorem}[defin]{Theorem}
\newtheorem{thrme}{Th\'eor\`eme}
\newtheorem{lemma}[defin]{Lemma}
\newtheorem{Lemma}[defin]{Lemma}
\newtheorem{Lemma1}[defin1]{Lemma}
\newtheorem{proposition}[defin]{\rm PROPOSITION}
\newtheorem{Proposition}[defin]{\rm PROPOSITION}
\newtheorem{prop}{\rm PROPOSITION}
\newtheorem{corollary}[definition]{\rm Corollary}
\newtheorem{Corollary}[defin]{\rm Corollary}
\newtheorem{Cor}[defin1]{\rm Corollary}
\newtheorem{examples}[definition]{Examples}
\newtheorem{exercise}{Exercise}[section]
\newtheorem{notitle}[definition]{\hskip -3pt}
\newtheorem{notitle1}[defin]{\hskip -3pt}
\newtheorem{notitle2}[defin1]{\hskip -3pt}
\newtheorem{notation}[definition]{Notation}
\newtheorem{notation1}[defin]{Notation}
\newtheorem{Remark}[defin1]{Remark}
\newtheorem{Rem}[defin]{Remark}
\newtheorem{Rems}[defin]{Remarks}
\newtheorem{oquestion}[definition]{Open question}
\newtheorem{question}[definition]{Question}
\newtheorem{oques}[defin]{Open question}
\newtheorem{remark}[defin]{Remark}
\newtheorem{Remark1}[defin]{Remark}
\newtheorem{assumption}[defin]{Assumption}
\newtheorem{counterexample}[definition]{(Counter)example}
\newtheorem{construction}[definition]{Construction}
\newtheorem{example}[definition]{Example}
\def\@begintheorem#1#2{\theoremfont \trivlist
        \item[\hskip \labelsep{\it #1\ {\rm #2.}}]\@thmfont}
\def\@opargbegintheorem#1#2#3{\theoremfont \trivlist
        \item[\hskip \labelsep{\it #1\ {\bf #2}\ #3.}]\@thmfont}
\def\@oparbegintheorem#1#2#3#4{\theoremfont \trivlist
        \item[\hskip \labelsep{\it #1\ { #2}\ #3 #4}]\@thmfont}





%%

\endinput
%% 
%% End of file `mat01.cls'.


