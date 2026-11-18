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
beginfig(48)
  obj(PmF)("P\fix F");
  obj(Px)("Px");
  obj(mF)("\fix F");
  obj(x)("x");

  origin
    = loc(mF)
    = loc(Px) + 3u*left + u*down;

  canonical_rectangle(locs(PmF, Px, x, mF));

  drop(PmF, Px, x, mF);

  mor(PmF, Px)("P(\fold f)", top);
  mor(Px, x)("a", rt);
  mor(PmF, mF)("\alg", lft);
  mor(mF, x)("\fold f", bot);

  commute(PmF, Px, x, mF);
endfig;

end
