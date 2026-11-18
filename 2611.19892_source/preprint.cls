%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Preprint / Postprint class                    %%
%% Author:  Bruno Bentzen                        %%
%% Version: 1.0.0                                %%
%% License: Apache license 2.0                   %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{preprint}[2020/05/20 Class designed for preprints and postprints]

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions \relax

\LoadClass[12pt,a4paper]{article} 

\usepackage[
left=1.0in,right=1.0in,
top=1.0in,bottom=1.0in,
]{geometry}

\usepackage{amssymb,mathtools} 		% basic math stuff
\usepackage{hyperref} 				% enables hyperlinks
\usepackage[round]{natbib} 			% bibliography
\usepackage{titlesec}				% manipulates section titles
\usepackage{setspace}				% spacing
\usepackage{xcolor}					% colors
\usepackage{etoolbox}				% color link only in year
\usepackage{libertine}              % enables the Libertine font
\usepackage{parskip}
\usepackage{cleveref}
\usepackage{enumerate}

\setlength{\parskip}{2em}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Journal information                                                  %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\makeatletter
\newcommand{\journal}[1]{\renewcommand\@journal{#1}}
\newcommand{\@journal}{journal}
\newcommand{\volume}[1]{\renewcommand\@volume{#1}}
\newcommand{\@volume}{vol}
\newcommand{\issue}[1]{\renewcommand\@issue{#1}}
\newcommand{\@issue}{issue}
\newcommand{\pages}[1]{\renewcommand\@pages{#1}}
\newcommand{\@pages}{n--m}
\newcommand{\when}[1]{\renewcommand\@when{#1}}
\newcommand{\@when}{when}
\newcommand{\doi}[1]{\renewcommand\@doi{#1}}
\newcommand{\@doi}{10.0000/000000-0000}
\newcommand{\setdoi}[1]{\renewcommand\@setdoi{#1}}
\newcommand{\@setdoi}{\href{https://doi.org/\@doi}{\@doi}}
\newcommand{\info}[1]{\renewcommand\@info{#1}}
\newcommand{\@info}{ {\singlespacing
		\textit{\@journal} \\ 
		{\@volume}{\@issue} {\@pages}, {\@when} \\[-0.8em] 
		\@setdoi }
}
%\newcommand{\@info}{ \singlespacing
	%	\textit{\@journal} \\ 
	%	{\@volume}({\@issue}), pp.{\@pages}, {\@when} \\
	%	\@setdoi 
	%}
\newcommand{\runtitle}[1]{\renewcommand\@runtitle{#1}}
\newcommand{\@runtitle}{\@title}
\makeatother

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Title page                                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Title

\makeatletter             
\def\@maketitle{
	\raggedright
	\vspace*{-5em}
	\begin{flushright}
		{\small \@info }
	\end{flushright}
	\vspace*{0.8em}
	\begin{center}
		\begin{spacing}{1.1}
			\Large \bfseries \@title 
		\end{spacing} 
		\bigskip
		{\large  \@author} \\[.1ex] 
		\vspace*{1.2em}
\end{center}}
\makeatother

% Header

\makeatletter
\def\ps@mystyle{%
	\let\@oddfoot\@empty\let\@evenfoot\@empty
	\def\@oddhead{%
		\ifodd\value{page}\relax
		\hfill\runtitle\hfill\makebox[0pt][l]{\thepage}%
		\else
		\makebox[0pt][l]{\thepage}\hfill\@author\hfill%
		\fi%
	}%
	\let\@mkboth\markboth}
\makeatother
\pagestyle{mystyle}

% Abstract

\renewenvironment{abstract}
{\small
	\list{}{%
		\setlength{\leftmargin}{1mm}% 
		\setlength{\rightmargin}{\leftmargin}%
	}%
	\item\relax {\bfseries \abstractname~} }
{\endlist}

% Keywords

\newenvironment{keywords}
{\small
	\list{}{%
		\setlength{\leftmargin}{1mm}% 
		\setlength{\rightmargin}{\leftmargin}%
	}%
	\item\relax {\bfseries Keywords~}}
{\endlist}

\newcommand{\kwd}{$\cdot$~}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Author contact information                                           %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Address

\makeatletter
\newcommand{\university}[1]{\renewcommand\@university{#1}}
\newcommand{\@university}{s}
\newcommand{\department}[1]{\renewcommand\@department{#1}}
\newcommand{\@department}{}
\newcommand{\country}[1]{\renewcommand\@country{#1}}
\newcommand{\@country}{}
\newcommand{\email}[1]{\renewcommand\@email{#1}}
\newcommand{\@email}{}
\newcommand{\contactinfo}[1]{\renewcommand\@contactinfo{#1}}
\newcommand{\@contactinfo}{ \singlespacing
	\noindent\@department \\
	\@university \\
	\@country\\ 
	\href{mailto:\@email}{\@email} 
}
\newcommand{\address}{\par\vspace{\baselineskip}\@contactinfo}
\makeatother

% Acknowledgments

\newenvironment{acknowledgments}
{\par\vspace{\baselineskip} \noindent {\bfseries Acknowledgments~}}{\par\vspace{\baselineskip}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Main document                                                        %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Hyphenation

\tolerance=5000
\emergencystretch=\maxdimen
\hyphenpenalty=5000 
\hbadness=10000

% Footnote

\renewcommand*\footnoterule{}
\setlength{\skip\footins}{1.5pc plus 5pt minus 2pt}

% Sections

\titleformat{\section}
{\normalfont\fontsize{11}{15}\bfseries\filcenter}{\thesection}{1em}{}

\titleformat{\subsection}
{\normalfont\fontsize{10}{15}\bfseries\filcenter}{\thesubsection}{1em}{}

\titleformat{\subsubsection}
{\normalfont\fontsize{10}{15}\footnotesize\filcenter}{\thesubsubsection}{1em}{}


% Links

\definecolor{cobalt}{rgb}{0.0, 0.0, 0.80} 
\definecolor{ao(english)}{rgb}{0.0, 0.5, 0.0}

\hypersetup{
	colorlinks,
	linkcolor={ao(english)}, 
	citecolor={cobalt}, 
	urlcolor={ao(english)}  
}

% Genitive citation

\newcommand{\citepos}[1]{\begin{NoHyper}\citeauthor{#1}'s\end{NoHyper} (\citeyear{#1})}
\newcommand{\citeposp}[2]{\begin{NoHyper}\citeauthor{#1}'s\end{NoHyper} (\citeyear{#1}, #2)}

% Tilde in between author and year

\makeatletter
\def\NAT@spacechar{~}% new
\makeatother

% No hyperlinks in author's name (http://hosting.astro.cornell.edu/~tleung/wordpress/?p=287)

\makeatletter

% Patch case where name and year are separated by aysep
\patchcmd{\NAT@citex}
{\@citea\NAT@hyper@{%
		\NAT@nmfmt{\NAT@nm}%
		\hyper@natlinkbreak{\NAT@aysep\NAT@spacechar}{\@citeb\@extra@b@citeb}%
		\NAT@date}}
{\@citea\NAT@nmfmt{\NAT@nm}%
	\NAT@aysep\NAT@spacechar\NAT@hyper@{\NAT@date}}{}{}

% Patch case where name and year are separated by opening bracket
\patchcmd{\NAT@citex}
{\@citea\NAT@hyper@{%
		\NAT@nmfmt{\NAT@nm}%
		\hyper@natlinkbreak{\NAT@spacechar\NAT@@open\if*#1*\else#1\NAT@spacechar\fi}%
		{\@citeb\@extra@b@citeb}%
		\NAT@date}}
{\@citea\NAT@nmfmt{\NAT@nm}%
	\NAT@spacechar\NAT@@open\if*#1*\else#1\NAT@spacechar\fi\NAT@hyper@{\NAT@date}}
{}{}

\makeatother

% Notations

\DeclareFontFamily{U}{matha}{\hyphenchar\font45}
\DeclareFontShape{U}{matha}{m}{n}{
	<5> <6> <7> <8> <9> <10> gen * matha
	<10.95> matha10 <12> <14.4> <17.28> <20.74> <24.88> matha12
}{}
\DeclareSymbolFont{matha}{U}{matha}{m}{n}

\DeclareMathSymbol{\varsupset}{3}{matha}{"81} % inspired by https://tex.stackexchange.com/questions/14386/importing-a-single-symbol-from-a-different-font

\newcommand{\gga}{\textit{Grundgesetze}}
\newcommand{\bs}{\textit{Begriffsschrift}}
\newcommand{\gla}{\textit{Grundlagen}}

\newcommand{\prop}{\> \mathsf{prop}}
\newcommand{\type}{\> \mathsf{type}}
\newcommand{\true}{\> \mathsf{true}}
\newcommand{\val}{\> \mathsf{val}}
\newcommand{\ctx}{\> \mathsf{ctx}}
\newcommand{\pitype}[1]{{(#1)\to}}
\newcommand{\fun}[1]{\lambda #1.}
\newcommand{\nat}{\mathsf{nat}}
\newcommand{\zero}{\mathsf{0}}
\renewcommand{\succ}{\mathsf{succ}}
\newcommand{\natrec}{\mathsf{natrec}}

\newcommand{\refl}{\mathsf{refl}}
\newcommand{\eqrec}{\mathsf{eqrec}}
\newcommand{\shouldsf}[1]{#1}

%% End of file `preprint.cls'.