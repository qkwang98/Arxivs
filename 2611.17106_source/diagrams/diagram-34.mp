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
beginfig(34)
  obj(Fx)("Fx");
  obj(FPEx)("FPEx");
  obj(PFEx)("PFEx");
  obj(PEFx)("PEFx");

  origin
    = loc(PEFx)
    = loc(FPEx) + 3u*left + u*down;

  canonical_rectangle(locs(Fx, FPEx, PFEx, PEFx));

  drop(Fx, FPEx, PFEx, PEFx);

  mor(FPEx  , Fx)("F\epsilon", top);
  mor(PFEx, FPEx)("\strength", rt);
  mor(PEFx  , Fx)("\epsilon", lft);
  mor(PFEx, PEFx)("P\costrength", bot);

  commute(Fx, FPEx, PFEx, PEFx);
endfig;

end
