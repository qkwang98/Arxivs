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
beginfig(36)
  obj(FPx)("FPx");
  obj(PFx)("PFx");
  obj(PEFPx)("PEFPx");
  obj(PFEPx)("PFEPx");

  obj(PEPFEPx)("PEPFEPx");
  obj(FPEPx)("FPEPx");
  obj(PEFPEx)("PEFPEx");
  obj(PFEPy)("PFEPx");
  obj(FPy)("FPx");

  origin
    = loc(PFx)
    = loc(PEFPx) + 7.5u*left + 4u*down;

  canonical_rectangle(locs(FPx, PEFPx, PFEPx, PFx));

  evenly_spaced(loc(PFEPx), z1, loc(PEPFEPx), z2, loc(FPEPx), z3, loc(FPx));
  canonical_rectangle(locs(FPEPx, PEFPEx, PEPFEPx, PFEPy));
  evenly_spaced(loc(PFx), loc(FPy), z3);

  drop(FPx, PEFPx, PFEPx, PFx, PEPFEPx, FPEPx, PEFPEx, PFEPy, FPy);

  curved_mor(PFx, FPx)("\strength", lft) lftstr;
  mor(PEFPx, FPx)("\epsilon", top);
  mor(PFEPx,PEFPx)("P\costrength", rt);
  mor(PFx, PFEPx)("PF\eta", bot);

  mor(PFx, FPy)("\strength", lrt);
  mor(FPy, FPEPx)("FP\eta", ulft);
  mor(FPEPx, FPx)("F\epsilon", urt);
  equals_mor(FPy, FPx)("",);

  equals_mor(PFEPx, PFEPy)("",);
  mor(PFEPx, PEPFEPx)("P\eta", urt);
  mor(PEPFEPx, PFEPy)("\epsilon", bot);

  mor(PFEPy, FPEPx)("\strength", lft);
  mor(PEPFEPx, PEFPEx)("PE\strength", rt);
  mor(PEFPEx, FPEPx)("\epsilon", top);

  mor(PEFPEx, PEFPx)("PEF\epsilon", ulft);

  commute_explained(PFEPy, PEFPEx)("$\epsilon$ nat");
  commute_explained(PFEPx, PEFPx, PEFPEx)("$P(\defines)$");
  commute_explained(FPEPx, PEFPEx, PEFPx, FPx)("$\epsilon$-nat");
  commute_explained(FPEPx, FPy, FPx)("$F($adjunction$)$");
  commute_explained(PFx, PFEPy, PFEPx)("$\strength$-nat");

  commute(lftstr, FPy);

endfig;

end
