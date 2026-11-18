input okdefs;
input commutative_diagrams;

TEXPRE(
  ""                           & char(10) &
  "%&latex"                    & char(10) &
  "\PassOptionsToPackage{usenames,dvipsnames,svgnames,table}{xcolor}" &
                                 char(10) &
  "\documentclass[10pt]{article}"    & char(10) &
  "\usepackage{okgeneralmath}" & char(10) &
  "\usepackage{okcategory}"    & char(10) &
  "\usepackage{libertine}"     & char(10) &
  "\input{defs}"               & char(10) &
  "\begin{document}"           & char(10) &
  ""
  );

outputtemplate := "diagram-%2c.mps";
beginfig(51)
  obj(A)("\carrier A \ni a");
  obj(B)("\carrier\B \ni f_{\ctx} a");
  obj(GA)("\pair-{g}{\inv g \iact\ctx a} \in \gast\carrier \A");
  obj(GB)("\pair-{g}{\inv g \iact\ctx fa} = \pair-{g}{f(\inv g \iact \ctx a)} \in \gast\carrier \B");

  origin
    = loc(B)
    = loc(GA) + 6u*left + 1.5u* down;

  canonical_rectangle(locs(A, GA, GB, B));

  drop(A, B, GB, GA);

  map(A,B)("f_{\ctx}", lft);
  map(GA,GB)("(\gast f)_{\ctx}", rt);
  map(A, GA)("(g \iact\ctx)", top);
  map(B, GB)("(g \iact\ctx)", bot);

  commute_explained(A,B, GA, GB)("$f$ equivariant");
endfig;

end
