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
beginfig(18)
  obj(FmF)("F\fix F");
  obj(mF)("\fix F");
  obj(FXA)("F(X^A)");
  obj(XA)("X^A");

  origin
    = loc(mF)
    = loc(FXA)  + 3u*left + u*down;

  canonical_rectangle(locs(FmF, FXA, XA, mF));
  drop(FmF, FXA, XA, mF);

  mor(FmF, FXA)("Fk", top);
  mor(FXA, XA)("h", rt);
  mor(FmF, mF)("\roll", lft);
  dashed_mor(mF, XA)("k", bot);

  commute_explained(FmF, FXA, XA, mF)("($*$)");
endfig;

end
