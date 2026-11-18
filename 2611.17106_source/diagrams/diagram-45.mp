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
beginfig(45)
  obj(mFa)("\fix F");
  obj(mFb)("\fix F");
  obj(PmF)("P\fix F");

  obj(FmFa)("F\fix F");
  obj(FmFb)("F\fix F");
  obj(FPmF)("FP\fix F");
  obj(PFmF)("PF\fix F");

  obj(dummy)("");

  origin
    = z1
    = loc(mFb) + 8u*left + 3u*down;

  canonical_rectangle(z1, z2, loc(mFb), loc(mFa));
  loc(PmF) = .5[z1,z2];

  y3 = y4 = ypart(loc(mFa) + .75u*up);
  x3 = xpart(loc(mFa));
  x4 = xpart(loc(mFb));

  z5 = .5[z3,z4];

  evenly_spaced(z5, z6, loc(FPmF), z7, loc(PmF));
  evenly_spaced(loc(mFa), z8, loc(PFmF), loc(PmF));
  evenly_spaced(locs(mFa, FmFa, dummy, FmFb, mFb));

  drop(mFa, mFb, PmF, FmFa, FmFb, FPmF, PFmF);

  explicit_equals_mor(mFa, mFb)(loc(mFa) -- z3 -- z4 -- loc(mFb))("",) eqtop;
  explicit_mor(mFa, PmF)(loc(mFa) -- z1 -- loc(PmF))("\eta",bot);
  explicit_mor(PmF, mFb)(loc(PmF) -- z2 -- loc(mFb))("\alg",bot);

  mor(FmFa, mFa)("\roll", bot);
  mor(FmFb, mFb)("\roll", bot);
  equals_mor(FmFa, FmFb)("",);
  mor(FmFa, FPmF)("F\eta", urt);
  mor(FPmF, FmFb)("F\alg", ulft);
  mor(FmFa, PFmF)("\eta", llft);
  mor(PFmF, PmF)("P\roll", llft);
  mor(PFmF, FPmF)("\strength", lrt);

  commute_explained(mFa, PFmF)("$\eta$-nat");
  commute_explained(FmFa, FPmF, PFmF)("$P$-strength");
  commute_gen(FmFa, FmFb, FPmF)("\text{IH}");
  commute_explained(PmF, mFb)("$\alg$-def by\\$P$ initiality");
  commute(eqtop, FmFa, FmFb);
endfig;

end
