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
beginfig(42)
  obj(Fx)("Fx");
  obj(PFx)("PFx");
  obj(FPx)("FPx");

  origin
    = loc(Fx)
    = loc(PFx) + u*left + u*down;
  loc(FPx) = loc(Fx) reflectedabout(loc(PFx), loc(PFx) + u*down);

  drop(Fx, PFx, FPx);

  mor(Fx, PFx)("\eta", ulft);
  mor(PFx, FPx)("\strength", urt);
  mor(Fx, FPx)("F\eta", bot);

  commute(Fx, PFx, FPx);
endfig;

end
