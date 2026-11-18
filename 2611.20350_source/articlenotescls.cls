%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Article notes class based on scrartcl class
%% Version : 1.10
%% Purpose : Designed for ease and minimalism and primarily used to create well typed "articlish" notes. 
%% Author : Varinderjit Mann
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%=================================
% Basic Frame
%=================================

\NeedsTeXFormat{LaTeX2e} %this is more or less a reference on the minimal requirement to compile this file
\ProvidesClass{articlenotescls}[2025/10/13 - minimal notes class] %naming the class

\LoadClass[DIV=12, fontsize=11.0pt]{scrartcl}
\KOMAoptions{abstract=false} %abstract true provides the abstract heading but messes up fontsize
\KOMAoptions{titlepage=false} %titlepage false is to be used without titlepage environment
\KOMAoptions{toc=bibliography, toc=index, toc=graduated}
\KOMAoptions{footnotes=multiple, parskip=half}

\RequirePackage[utf8]{inputenc} %your text file input encoding, just keep it even if not necessary
\RequirePackage[T1]{fontenc} %font output encoding, just keep it even if not necessary

%=================================
% Font and Math
%=================================

\RequirePackage{amsmath,amssymb,mathtools} %amssymb loads amsfont
\RequirePackage{amsthm}
%\RequirePackage{thmtools} %at some point it was needed for a bugfix, maybe?

%\RequirePackage{lmodern} %just to obtain scalable computer modern font which can be substituted arbitrarily to avoid any font warnings
\RequirePackage{libertinus}

%\RequirePackage{newtxtext} %no math font
%\RequirePackage{newtxmath} %mathfont, doesn't alter text font
\RequirePackage{dsfont} %best blackboard font, doesn't replace \mathbb and uses \mathds, doesn't contain bboard Delta though

%\setkomafont{disposition}{\normalfont\bfseries} %heading changes

\DeclareFontFamily{U}{dmjhira}{}
\DeclareFontShape{U}{dmjhira}{m}{n}{
  <-> * dmjhira
}{}
\DeclareSymbolFont{dmjhira}{U}{dmjhira}{m}{n}
\DeclareMathSymbol{\Yo}{0}{dmjhira}{"48} %hiragana Yo

\RequirePackage[protrusion=true,expansion=true]{microtype}

%=================================
% Hyperlinks and Reference
%=================================

\RequirePackage[dvipsnames]{xcolor}
\newcommand\myshade{90}
\colorlet{mylinkcolor}{MidnightBlue}
\colorlet{mycitecolor}{MidnightBlue}
\colorlet{myurlcolor}{NavyBlue}

\RequirePackage[backref=page]{hyperref} %backref can't be hypersetuped
\RequirePackage{cleveref} %cleveref after hyperref
\hypersetup{
	linkcolor  = mylinkcolor!\myshade!black,
	citecolor  = mycitecolor!\myshade!black,
	urlcolor   = myurlcolor!\myshade!black,
	colorlinks = true,
}

\renewcommand\backreftwosep{, } %entry sep entry
\renewcommand\backrefsep{, }  % .... entry sep entry ....
\renewcommand\backreflastsep{, } % ....entry sep entry
\renewcommand*{\backrefalt}[4]{%
	\ifcase #1%
	\or \textcolor{Gray!80}{p.}~#2%
	\else \textcolor{Gray!80}{pp.}~#2%
	\fi%
}

\makeatletter
	\newcommand{\hypertargetraisefix}[1]{\Hy@raisedlink{\hypertarget{#1}{}}} %fixes link height but might break on newpage margins
\makeatother

\newcommand{\hyperbilinkto}[2]{\hyperlink{#1f}{#2}\hypertargetraisefix{#1b}{}} %target after to have compatibility with enum
\newcommand{\hyperbilinkfrom}[2]{\hyperlink{#1b}{#2}\hypertargetraisefix{#1f}{}} %target after to have compatibility with enum

\newcommand{\tpdf}[1]{\texorpdfstring{#1}{TEXT}} %very important for creating headings whilst using hyperref

%=================================
% Bibliography & Index
%=================================

\RequirePackage{makeidx} %use tools->makeindex in texstudio
\makeindex %this generates .idx file and not .ind file

\RequirePackage[square,numbers]{natbib} %square bracket with numbers
\bibliographystyle{abbrvnat}

%=================================
% Diagrams
%=================================

\RequirePackage{graphicx}
\RequirePackage{tikz}
\usetikzlibrary{arrows,positioning,calc,cd,nfold}
\RequirePackage{quiver} %allows for support with quiver.com 
\RequirePackage{adjustbox} %allows for adjusting diagrams

\tikzcdset{
  inline diagram/.style={
    cramped,
    baseline=0pt
  },
  punctuated display/.style={
    baseline=(current bounding box.south)
  }
} % a tikz command template for punctuaton

%=================================
% Utilities
%=================================

\RequirePackage{comment} % provides the comment environment
\RequirePackage{csquotes} % provides quotations
\RequirePackage{enumitem} % provides modernized enumerate

%=================================
% Theorem
%=================================

\theoremstyle{definition} %upright
\newtheorem{definition}{Definition}[subsection] %subsection reset counter
\makeatletter
	\renewcommand*{\theHdefinition}{\theHsubsection.\arabic{definition}} %bugfix
\makeatother
\newtheorem{example}[definition]{Example} %[] implies a shared counter
\newtheorem*{definition*}{Definition} %unnumbered
\newtheorem*{example*}{Example} %unnumbered

\theoremstyle{plain} %italicised
\newtheorem{theorem}[definition]{Theorem}
\newtheorem{corollary}[definition]{Corollary}
\newtheorem{lemma}[definition]{Lemma}
\newtheorem{proposition}[definition]{Proposition} 
\newtheorem*{theorem*}{Theorem}	%unnumbered
\newtheorem*{corollary*}{Corollary}	%unnumbered
\newtheorem*{lemma*}{Lemma} %unnumbered
\newtheorem*{proposition*}{Proposition} %unnumbered

\theoremstyle{remark} %italicsed heading with upright body
\newtheorem{remark}[definition]{Remark}
\newtheorem*{remark*}{Remark} %unnumbered

%=================================
% Header and Footer 
%=================================

\RequirePackage{scrlayer-scrpage}
\automark{section}
\ihead{}
\chead{}
\ohead{\headmark}
\ifoot{}
\cfoot{\pagemark}
\ofoot{}

\renewcommand*{\titlepagestyle}{empty} %only relevant for in-page style
\renewcommand*{\indexpagestyle}{empty}
%\renewcommand*{\partpagestyle}{empty}
%\renewcommand*{\chapterpagestyle}{empty}
%The asterisk is just an error checking mechanism to disallow \par

%=================================
% Periods and punctuations in diagrams
%=================================

\RequirePackage{ifthen}

\newboolean{cdbaselineon}
\setboolean{cdbaselineon}{false} % default: off

\AtBeginDocument{%
	\ifthenelse{\boolean{cdbaselineon}}{%
	  % Apply baseline=(current bounding box.south) to all tikz-cd diagrams
	  \tikzcdset{every diagram/.append style={baseline=(current bounding box.south)}}%
	}{%
	  % Do nothing, keep default
	}%
}

\newboolean{showcdpunctuation}
\setboolean{showcdpunctuation}{false} % default: off

% Macro for conditional period after a diagram
\newcommand{\cdpunct}[2][0pt]{%
  \ifthenelse{\boolean{showcdpunctuation}}%
    {\mathpunct{\raisebox{#1}{#2}}}%
    {}%
}
