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
beginfig(32)
  obj(FPx)("FPx");
  obj(PFx)("PFx");
  obj(PEFPx)("PEFPx");
  obj(PFEPx)("PFEPx");

  origin
    = loc(PFx)
    = loc(PEFPx) + 2u*left + u*down;

  canonical_rectangle(locs(FPx, PEFPx, PFEPx, PFx));
  drop(FPx, PEFPx, PFEPx, PFx);

  mor(PFx, FPx)("\strength", lft);
  mor(PEFPx, FPx)("\epsilon", top);
  mor(PFEPx,PEFPx)("P\costrength", rt);
  mor(PFx, PFEPx)("PF\eta", bot);

  commute_gen(FPx, PEFPx, PFEPx, PFx)("\definedby");
endfig;

end
