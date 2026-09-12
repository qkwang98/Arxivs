%%% ====================================================================
%%% @LaTeX-file{
%%%    filename  = "kms-c.cls",
%%%    version   = "0.5.2",
%%%    date      = "2021/06/27",,
%%%
%%%    author    = "Gihyun Park",
%%%    copyright = "KMS",
%%%    address   = "",
%%%    email     = "",
%%%    abstract  = "This is a LaTeX documentclass for the new style of
%%%                 Journal of the Korean Mathematical Society.",
%%% }
%%% ====================================================================
\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{kms-c}[2009/03/16 v0.4 Communications of KMS documentclass]

\newif\if@usekotex\@usekotexfalse
\DeclareOption{kotex}{\@usekotextrue}

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{amsart}}
\ProcessOptions\relax

\LoadClass[a4paper]{amsart}[2004/08/06]
\def\Author{\author}
\if@usekotex
\RequirePackage[finemath]{kotex}
\RequirePackage{dhucs-setspace}[2005/03/04]
\setstretch{1.2}
%\SetHangulFonts{ynmj}{yngt}{untz}
%\SetHanjaFonts{ynmj}{yngt}{yngt}
%%% ====================================================================
%%% Modifications from amsart.cls 2.20 (2004/08/06) for kotex
%%% ====================================================================
%%% Line 261: adjust \normalparindent and \parindent for Hangul
\normalparindent=10pt
\parindent=\normalparindent
%%% Line 316: adjust heading font size
\def\ps@headings{\ps@empty
  \def\@evenhead{%
    \setTrue{runhead}%
    \normalfont\footnotesize
    \rlap{\thepage}\hfil
    \def\thanks{\protect\thanks@warning}%
    \leftmark{}{}\hfil}%
  \def\@oddhead{%
    \setTrue{runhead}%
    \normalfont\footnotesize \hfil
    \def\thanks{\protect\thanks@warning}%
    \rightmark{}{}\hfil \llap{\thepage}}%
  \let\@mkboth\markboth
}
%%% Line 415: deactivate \uppercasenonmath
\let\uppercasenonmath\@gobble
%%% Line 441: deactivate \MakeUpperCase
\let\MakeUpperCase\@gobble
%%% Line 607: remove AND between author names
\renewcommand{\andify}{\nxandlist{\unskip, }{\unskip, }{\unskip, }}
%%% Line 609: remove AND between author names
\renewcommand{\and}{\unskip, \ignorespaces}
%%% Line 789: change \abstractname to Hangul
%\renewcommand{\abstractname}{{\upshape 요약}}
%%% Line 802: use larger font size for Hangul title
\def\@settitle{\begin{center}%
  \baselineskip14\p@\relax
  \large\bfseries
  \@title
  \end{center}%
}
%%% Line 809: remove AND between author names
\renewcommand{\author@andify}{%
  \nxandlist{\unskip ,\penalty-1 \space\ignorespaces}%
    {\unskip , \space}%
    {\unskip ,\penalty-2 \space}%
}
%%% Line 844: remove abstractname
\renewenvironment{abstract}{%
  \ifx\maketitle\relax
    \ClassWarning{\@classname}{Abstract should precede
      \protect\maketitle\space in AMS document classes; reported}%
  \fi
  \global\setbox\abstractbox=\vtop \bgroup
    \normalfont\Small
    \list{}{\labelwidth\z@
      \leftmargin3pc \rightmargin\leftmargin
      \listparindent\normalparindent \itemindent\z@
      \parsep\z@ \@plus\p@
      \let\fullwidthdisplay\relax
    }%
    \item[]%
}{%
  \endlist\egroup
  \ifx\@setabstract\relax \@setabstracta \fi
}
%%% Line 1152: change \contentsnamefont
\renewcommand{\contentsnamefont}{\sffamily}
%%% Line 1170: change \contentsname
\def\contentsname{목차}
\def\listfigurename{그림 목차}
\def\listtablename{표 목차}
%%% Line 1248: change \refname to Hangul
\renewcommand{\refname}{참고 문헌}
%%% Line 1269: restore the baselinestretch for bibliography
\renewcommand{\@bibtitlestyle}{%
  \setstretch{1.0}\@xp\section\@xp*\@xp{\refname}%
}
%%% Line 1360: change caption head font
\def\@captionheadfont{\upshape}
%%% Line 1365: change \figurename to Hangul
\def\figurename{그림}
%%% Line 1380: change \figurename to Hangul
\def\tablename{표}
%%% Line 1606: change the plain theorem style
\def\th@plain{%
  \thm@headfont{\sffamily}
  \sffamily
}
%%% Line 1616: change the definition theorem style
\def\th@definition{%
  \thm@headfont{\sffamily}
  \normalfont
}
%%% Line 1619: change the remark theorem style
\def\th@remark{%
  \thm@headfont{\bfseries}
  \normalfont
}
%%% Line 1816: change the proof style
\renewenvironment{proof}[1][\proofname]{\par
  \pushQED{\qed}%
  \normalfont \topsep6\p@\@plus6\p@\relax
  \trivlist
  \item[\hskip\labelsep
        \sffamily
    #1.]\ignorespaces
}{%
  \popQED\endtrivlist\@endpefalse
}
%%% Line 1826: change \proofname in Hangul
\renewcommand{\proofname}{증명}
%%% Line 1910: reset \pagestyle
\pagestyle{headings}
\fi
%%% ====================================================================
%%% Modifications from amsart.cls 2.20 (2004/08/06)
%%% ====================================================================
\def\volinfo{%
  {\bfseries\currentvolume} (\currentyear), No.~\number0\currentissue
}
\def\ArticleNo#1{\def\@articleNo{#1}}
\def\pageinfo{%
  \ifnum\start@page=\z@
    pp.~000--000
  \else
    \ifx\start@page\end@page
      p.~\start@page
    \else
      pp.~\start@page--\end@page
    \fi
  \fi
}
\def\received#1{\def\@received{#1}}
\let\@received=\@empty
\def\@setreceived{\@received\@addpunct.}
%%% Line 127: change \newline to \space and delete \@dateposted
\def\article@logo{%
  \set@logo{%
    \publname
    \ifx\@empty\currentvolume
    \else\space\volinfo, \pageinfo
%%% Support DOI (2009/03/16)
      \ifx\@empty\currentissue
      \else\par\doiname.\@articleNo \par \issnname
      \fi
    \fi
  }%
}
%%% Line 145: change \fontsize{6}{7\p@} to \footnotesize
\def\@logofont{\footnotesize}
%%% Line 240: change \textheight and \textwidth
%%%           but do not touch \headheight, \footskip, and \parindent, etc.
\textwidth=120mm
\textheight=185mm
%%% Line 534: changed only the 538th line for \\
\def\@setaddresses{\par
  \nobreak \begingroup
  \footnotesize
  \def\author##1{\nobreak\addvspace\bigskipamount}%
  \def\\{\par\nobreak}%
  \interlinepenalty\@M
  \def\address##1##2{\begingroup
    \par\addvspace\bigskipamount\indent
    \@ifnotempty{##1}{(\ignorespaces##1\unskip) }%
    {\if@usekotex\else\scshape\fi\ignorespaces##2}\par\endgroup}%
  \def\curraddr##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak\indent\curraddrname
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
      ##2\par}\endgroup}%
  \def\email##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak\indent\emailaddrname
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
      \ttfamily##2\par}\endgroup}%
  \def\urladdr##1##2{\begingroup
    \def~{\char`\~}%
    \@ifnotempty{##2}{\nobreak\indent\urladdrname
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
      \ttfamily##2\par}\endgroup}%
  \addresses
  \endgroup
}
%%% Line 565: make the default from 2000 to 2020
\renewcommand*\subjclass[2][2020]{%
  \def\@subjclass{#2}%
  \@ifundefined{subjclassname@#1}{%
    \ClassWarning{\@classname}{Unknown edition (#1) of Mathematics
      Subject Classification; using '2020'.}%
  }{%
    \@xp\let\@xp\subjclassname\csname subjclassname@#1\endcsname
  }%
}
%%% Line 631: add \do\received and \do\@received
\def\@cleartopmattertags{%
  \def\do##1{\let##1\relax}%
  \do\maketitle \do\@maketitle \do\title \do\@xtitle \do\@title
  \do\author \do\@xauthor \do\address \do\@xaddress
  \do\contrib \do\contribs \do\xcontribs \do\toccontribs
  \do\email \do\@xemail \do\curraddr \do\@xcurraddr
  \do\commby \do\@commby
  \do\dedicatory \do\@dedicatory \do\thanks \do\thankses
  \do\keywords \do\@keywords \do\subjclass \do\@subjclass
  \do\received \do\@received
}
%%% Line 642: adjust \topskip from 42\p@ to 30.5\p@ (646th line)
\def\ps@titlepage{\ps@plain
  \let\@oddfoot\@empty \let\@evenfoot\@empty
  \def\@oddhead{\@serieslogo\hss}%
  \let\@evenhead\@oddhead % in case an article starts on a left-hand page
}
\def\@maketitle{%
  \if@titlepage
    \addtocounter{page}\m@ne
    \thispagestyle{titlepage}
    \normalfont\normalsize
    \global\topskip38.5\p@\relax % around 4pc % changed from 30.5 to 38.5 for DOI (2009/03/16)
    \@settitle
    \ifx\@empty\authors \else \@setauthors \fi
    \vfill
    \baselineskip14\p@
    \vtop{\centering{%
      Reprinted from the\@@par
      Communications of the Korean Mathematical Society\@@par
      Vol.~\currentvolume, No.~\number0\currentissue,\space
      \ifcase\currentmonth\or
      January\or February\or March\or April\or May\or June\or
      July\or August\or September\or October\or November\or December\fi
      \ \currentyear
    }}
    \newpage
    \par
    \@topnum\z@ % this prevents figures from falling at the top of page 1
    \@setcopyright
    \thispagestyle{firstpage}
  \fi
  \normalfont\normalsize
  \@adminfootnotes
  \@mkboth{\@nx\shortauthors}{\@nx\shorttitle}%
  \global\topskip38.5\p@\relax % around 4pc % changed from 30.5 to 38.5 for DOI (2009/03/16)
  \@settitle
  \ifx\@empty\authors \else \@setauthors \fi
  \ifx\@empty\@dedicatory
  \else
    \baselineskip18\p@
    \vtop{\centering{\footnotesize\itshape\@dedicatory\@@par}%
      \global\dimen@i\prevdepth}\prevdepth\dimen@i
  \fi
  \@setabstract
  \normalsize
  \dimen@34\p@ \advance\dimen@-\baselineskip
  \vskip\dimen@\relax
} % end \@maketitle
%%% Line 664: add \@received field
\def\@adminfootnotes{%
  \let\@makefnmark\relax  \let\@thefnmark\relax
  \ifx\@empty\@date\else \@footnotetext{\@setdate}\fi
  \ifx\@empty\@received\else \@footnotetext{\@setreceived}\fi
  \ifx\@empty\@subjclass\else \@footnotetext{\@setsubjclass}\fi
  \ifx\@empty\@keywords\else \@footnotetext{\@setkeywords}\fi
  \ifx\@empty\thankses\else \@footnotetext{%
    \def\par{\let\par\@par}\@setthanks}%
  \fi
}
%%% Line 814: change \footnotesize -> \small\scshape
%%%           change \@topsep34\p@ from \@topsep30\p@
%%%           do not apply \MakeUppercase to \authors (823th line)
\def\@setauthors{%
  \begingroup
  \def\thanks{\protect\thanks@warning}%
  \trivlist
  \centering\small\if@usekotex\else\scshape\fi \@topsep30\p@\relax
  \advance\@topsep by -\baselineskip
  \item\relax
  \author@andify\authors
  \def\\{\protect\linebreak}%
  \authors%
  \ifx\@empty\contribs
  \else
    ,\penalty-3 \space \@setcontribs
    \@closetoccontribs
  \fi
  \endtrivlist
  \endgroup
}
%%% Line 1055: change \mdseries to \bfseries
\def\@secnumfont{\bfseries}
%%% Line 1119: changes part, specialsection, section, and subsection
%%%            specialsection will be used for References
\def\section{\@startsection{section}{1}%
  \z@{.7\linespacing\@plus\linespacing}{.5\linespacing}%
  {\normalfont\bfseries\centering}}
\def\subsection{\@startsection{subsection}{2}%
  \z@{.5\linespacing\@plus.7\linespacing}{.5\linespacing}%
  {\normalfont\bfseries}}
%%% ====================================================================
%%% Added on 2021/06/27
%%% ====================================================================
\RequirePackage{graphicx}
\RequirePackage[hyphens]{url}
\RequirePackage{hyperref}
\hypersetup{bookmarkstype=none,colorlinks=true,citecolor=black,linkcolor=black,urlcolor=black}
\RequirePackage[noadjust]{cite}
\allowdisplaybreaks
%%% ====================================================================
\endinput
