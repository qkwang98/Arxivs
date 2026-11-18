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
beginfig(44)
  obj(mFa)("\fix F");
  obj(mFb)("\fix F");
  obj(PmF)("P\fix F");

  origin
    = loc(mFa)
    = loc(PmF) + 2u*left + u*down;

  loc(mFb) = loc(mFa) reflectedabout(loc(PmF), loc(PmF) + u*down);

  drop(mFa, mFb, PmF);

  mor(mFa, PmF)("\eta", ulft);
  mor(PmF, mFb)("\alg", urt);
  equals_mor(mFa, mFb)("", );

  commute(PmF, mFa, mFb);
endfig;

end
