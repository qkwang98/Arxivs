\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{standard}

\newcommand{\innerclass}{article}
\def\showsolution{0}
\def\defsection{0}
\def\defamsart{0}

\DeclareOption{exam}{\renewcommand{\innerclass}{exam}}
\DeclareOption{amsart}{\renewcommand{\innerclass}{amsart}
\PassOptionsToClass{a4paper, 10pt, final}{amsart}
\def\defamsart{1}
}
\DeclareOption{answers}{\def\showsolution{1}}
\DeclareOption{bysection}{\def\defsection{1}}
\DeclareOption{bysubsection}{\def\defsection{2}}
\ProcessOptions\relax

\if\showsolution1
    \PassOptionsToClass{answers}{exam}
\fi
\LoadClass{\innerclass}

\RequirePackage{amsmath, amssymb, amsthm}

\if\defamsart1
    \RequirePackage[a4paper, bottom=2cm]{geometry}
\fi


\DeclareMathOperator{\Hom}{Hom}
\DeclareMathOperator{\Aut}{Aut}
\DeclareMathOperator{\Inn}{Inn}
\DeclareMathOperator{\Out}{Out}
\DeclareMathOperator{\Syl}{Syl}
\DeclareMathOperator{\Sym}{Sym}
\DeclareMathOperator{\Alt}{Alt}

\DeclareMathOperator{\rank}{rank}
\DeclareMathOperator{\class}{class}

\DeclareMathOperator{\EAB}{EAB}

\DeclareMathOperator{\IBr}{IBr}
\DeclareMathOperator{\Bl}{Bl}
\DeclareMathOperator{\Irr}{Irr}

\DeclareMathOperator{\cl}{cl}
\DeclareMathOperator{\im}{im}
\DeclareMathOperator{\lcm}{lcm}

\DeclareMathOperator{\GL}{GL}
\DeclareMathOperator{\GU}{GU}
\DeclareMathOperator{\GO}{GO}
\DeclareMathOperator{\SL}{SL}
\DeclareMathOperator{\PGL}{PGL}
\DeclareMathOperator{\PSO}{PSO}
\DeclareMathOperator{\PS}{PS}
\DeclareMathOperator{\PSL}{PSL}
\DeclareMathOperator{\PGU}{PGU}
\DeclareMathOperator{\PSU}{PSU}
\DeclareMathOperator{\Dih}{Dih}
\DeclareMathOperator{\PSp}{PSp}

\DeclareMathOperator{\GF}{GF}
\DeclareMathOperator{\Sz}{Sz}
\DeclareMathOperator{\Frob}{Frob}
\DeclareMathOperator{\Sp}{Sp}
\DeclareMathOperator{\SO}{SO}
\DeclareMathOperator{\SU}{SU}

\DeclareMathOperator{\ST}{ST}


\newcommand{\F}{\mathbb{F}}

\renewcommand{\L}{\operatorname{L}}
\DeclareMathOperator{\U}{U}
\renewcommand{\S}{\operatorname{S}}
\renewcommand{\O}{\operatorname{O}}

\DeclareMathOperator{\sA}{A}
\DeclareMathOperator{\sB}{B}
\DeclareMathOperator{\sC}{C}
\DeclareMathOperator{\sD}{D}
\DeclareMathOperator{\sE}{E}
\DeclareMathOperator{\sF}{F}
\DeclareMathOperator{\sG}{G}

\DeclareMathOperator{\Ly}{Ly}
\DeclareMathOperator{\HN}{HN}

\DeclareMathOperator{\SD}{SD}

\DeclareMathOperator{\Spin}{Spin}

\newcommand{\calA}{\mathcal{A}}
\newcommand{\calB}{\mathcal{B}}
\newcommand{\calC}{\mathcal{C}}
\newcommand{\calD}{\mathcal{D}}
\newcommand{\calE}{\mathcal{E}}
\newcommand{\calF}{\mathcal{F}}
\newcommand{\calG}{\mathcal{G}}
\newcommand{\calO}{\mathcal{O}}
\newcommand{\calS}{\mathcal{S}}
\newcommand{\calL}{\mathcal{L}}
\newcommand{\calR}{\mathcal{R}}
\newcommand{\calU}{\mathcal{U}}

\newcommand{\normalIn}{\trianglelefteq}
\newcommand{\subnormalIn}{\trianglelefteq \trianglelefteq}

\theoremstyle{definition}

\if \defsection1
\newtheorem{definition}{Definition}[section]
\else 
    \if \defsection2
        \newtheorem{definition}{Definition}[subsection]
    \else 
        \newtheorem{definition}{Definition}
    \fi 
\fi

\newtheorem{example}[definition]{Example}
\newtheorem{hypothesis}[definition]{Hypothesis}

\theoremstyle{plain}
\newtheorem{theorem}[definition]{Theorem}
\newtheorem{lemma}[definition]{Lemma}
\newtheorem{proposition}[definition]{Proposition}
\newtheorem{corollary}[definition]{Corollary}