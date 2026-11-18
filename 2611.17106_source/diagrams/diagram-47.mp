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
  "\newcommand{\uplambda}{\mathord{\text{\usefont{U}{fsy}{m}{n}{\char `l}}}}"
                               & char(10) &
  "\usepackage{libertine}"     & char(10) &
  "\input{defs}"               & char(10) &
  "\begin{document}"           & char(10) &
  ""
  );

outputtemplate := "diagram-%2c.mps";
beginfig(47)
  obj(PPmF)("P^2\fix F");
  obj(PmFa)("P\fix F");
  obj(PmFb)("P\fix F");
  obj(mF)("\fix F");

  origin
    = loc(PmFa)
    = loc(PmFb) + 4u*left + u*down;

  canonical_rectangle(locs(PPmF, PmFb, mF, PmFa));

  drop(PPmF, PmFb, mF, PmFa);

  mor(PPmF, PmFa)("\mu", lft);
  mor(PmFa, mF)("\alg", bot);
  mor(PPmF, PmFb)("P\alg", top);
  mor(PmFb, mF)("\alg", rt);

  commute(PPmF, PmFb, mF, PmFa);
endfig;

end
