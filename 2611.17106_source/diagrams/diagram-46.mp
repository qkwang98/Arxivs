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
beginfig(46)
  obj(PPmF)("P^2\fix F");
  obj(PmFa)("P\fix F");
  obj(PmFb)("P\fix F");
  obj(mF)("\fix F");

  obj(FPPmF)("FP^2\fix F");
  obj(FPmFa)("FP\fix F");
  obj(FPmFb)("FP\fix F");
  obj(FmF  )("F\fix F");

  obj(PFPmF)("PFP\fix F");
  obj(PPFmF)("P^2F\fix F");
  obj(PFmFa)("PF\fix F");
  obj(PFmFb)("PF\fix F");
  obj(FPmF)("FP\fix F");

  origin
    = loc(PmFa)
    = loc(PmFb) + 9u*left + 5u*down;

  canonical_rectangle(locs(PPmF, PmFb, mF, PmFa));

  evenly_spaced(locs(PPmF, PPFmF, PFPmF, FPPmF, FmF, mF));
  canonical_rectangle(locs(FPPmF, FPmFb, FmF, FPmFa));
  canonical_rectangle(locs(PPFmF, PFmFb, FPmFb, PFmFa));

  drop(PFmFa, PFmFb, PPmF, PPFmF, PFPmF, FPPmF, FmF, mF, PmFb, PmFa, FPmFa, FPmFb);

  mor(PPmF, PmFa)("P\alg", lft);
  mor(PPmF, PmFb)("\mu", top);
  mor(PmFa, mF)("\alg", bot);
  mor(PmFb, mF)("\alg", rt);

  mor(PPFmF, PPmF)("P^2\roll", urt);
  mor(PPFmF, PFPmF)("P\strength", urt);
  mor(PFPmF, FPPmF)("\strength", urt);
  mor(FmF, mF)("\roll", urt);

  mor(PPFmF, PFmFb)("\mu", bot);
  mor(PFmFb, PmFb)("P\roll", ulft);
  mor(FPPmF, FPmFb)("F\mu", top);
  mor(FPmFb, FmF)("F\alg", rt);
  mor(FPPmF, FPmFa)("FP\alg", lft);
  mor(FPmFa, FmF)("F\alg", bot);

  mor(PFPmF, PFmFa)("PF\alg", ulft);
  mor(PFmFa, PmFa)("P\roll", lrt);

  mor(PFmFa, FPmFa)("\strength", llft);
  mor(PFmFb, FPmFb)("\strength", rt);

  commute_explained(PPmF, PFPmF, PFmFa)("$P(\alg$ def$)$");
  commute_explained(PFmFa, FPPmF)("$\strength$ nat");
  commute_gen(FPPmF, FmF)("\text{IH}");
  commute_explained(PFmFa, PmFa, mF)("$\alg$-def");
  commute_explained(FPmFb, PmFb, PFmFb)("$\alg$-def");
  commute_explained(PPmF, PPFmF, PFmFb, PmFb)("$\mu$ nat");
  commute_explained(PFPmF, PFmFb)("$P$-strength");
endfig;

end
