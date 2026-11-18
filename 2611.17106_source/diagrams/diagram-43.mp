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
beginfig(43)
  obj(PPFx)("P^2Fx");
  obj(FPPx)("FP^2x");
  obj(PFPx)("PFPx");
  obj(PFx)("PFx");
  obj(FPx)("FPx");

  origin
    = loc(PFx)
    = loc(FPPx) + 6u*left + u*down;

  canonical_rectangle(locs(PPFx, FPPx, FPx, PFx));
  evenly_spaced(locs(PPFx, PFPx, FPPx));
  drop(PPFx, FPPx, PFx, FPx, PFPx);

  mor(PPFx, PFPx)("P\strength", top);
  mor(PFPx, FPPx)("\strength", top);
  mor(FPPx, FPx)("F\mu", rt);
  mor(PPFx, PFx)("\mu", lft);
  mor(PFx, FPx)("\strength", bot);

  commute(PPFx, FPPx, PFx, FPx);
endfig;

end
