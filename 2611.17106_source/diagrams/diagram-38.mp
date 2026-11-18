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
beginfig(38)
  obj(FmF)("F\fix F");
  obj(mF )("\fix F");
  obj(FEx)("FEx");
  obj(Ex)("Ex");

  origin
    = loc(mF)
    = loc(FEx) + 3u*left + u*down;

  canonical_rectangle(locs(FmF, FEx, Ex, mF));
  drop(FmF, FEx, Ex, mF);

  mor(FmF, mF)("\roll", lft);
  dashed_mor(mF, Ex)("h", bot);
  mor(FmF, FEx)("Fh", top);
  mor(FEx, Ex)("g", rt);

  commute(FmF, FEx, Ex, mF);
endfig;

end
