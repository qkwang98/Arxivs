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
beginfig(39)
  obj(PFmF)("PF\fix F");
  obj(FPmF)("FP\fix F");
  obj(PmF )("P \fix F");
  obj(Fx)("Fx");
  obj(Ox)(" x");

  obj(PFEx)("PFEx");
  obj(FPEx)("FPEx");
  obj(PEFx)("PEFx");
  obj(PEx)("PEx");

  origin
    = loc(PmF)
    = loc(Fx) + 8u*left + 5u*down;

  z1 = .5[loc(PmF), loc(Ox)];

  canonical_rectangle(locs(PFmF, Fx, Ox, PmF));
  evenly_spaced(locs(PFmF, FPmF, Fx));
  evenly_spaced(loc(PFmF), loc(PFEx), z2, z1);

  evenly_spaced(locs(PFEx, FPEx, Fx));
  evenly_spaced(loc(PFEx), loc(PEFx), loc(Ox));
  evenly_spaced(locs(PmF, PEx, PEFx));

  drop(PFmF, Fx, Ox, PmF, FPmF, FPEx, PFEx, PEx, PEFx);

  mor(PFmF, PmF)("P\roll", lft);
  dashed_mor(PmF, Ox)("\pfold f", bot);
  mor(PFmF, FPmF)("\strength", top);
  mor(FPmF, Fx)("F(\pfold f)", top);
  mor(Fx, Ox)("f", rt);

  mor(PFmF, PFEx)("PFh", urt);
  mor(PFEx, FPEx)("\strength", ulft);
  mor(FPmF, FPEx)("FPh", llft);
  mor(FPEx, Fx)("F\epsilon", lrt);
  mor(PFEx, PEFx)("P\costrength", urt);
  mor(PEFx, Fx)("\epsilon", lrt);
  mor(PEFx, PEx)("PEf", lrt);
  mor(PEx, Ox)("\epsilon", urt);
  mor(PmF, PEx)("Ph", ulft);
  mor(PFEx, PEx)("Pg", llft);

  commute_explained(PEx, Ox, Fx)("$\epsilon$ nat");
  commute_explained(PEFx, PFEx, PEFx, FPEx, Fx)("Strength-Costrength\\Lemma");
  commute_explained(FPmF, FPEx, Fx)("$F(\definedby)$");
  commute_explained(PFEx, PEFx, PEx)("$P(\definedby)$");
  commute_explained(PEx, PFmF, PmF)("$P(h$-def$)$");
  commute_explained(FPmF, PFEx, PFmF, FPEx)("$\strength$-nat");
  commute_gen(PmF, PEx, Ox)("\definedby");
endfig;

end
