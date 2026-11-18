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
beginfig(49)
  obj(PmF)("P\fix F");
  obj(Px)("Px");
  obj(mF)("\fix F");
  obj(ox)("x");

  obj(FPmF)("FP\fix F");
  obj(FPx )("FPx");
  obj(FmF )("F\fix F");
  obj(Fx  )("Fx");

  obj(PFmF)("PF\fix F");
  obj(PFx)("PFx");
  origin
    = loc(mF)
    = loc(Px) + 9u*left + 5u*down;

  canonical_rectangle(locs(PmF, Px, ox, mF));

  evenly_spaced(locs(PmF, PFmF, FPmF, Fx, ox));
  canonical_rectangle(locs(FPmF, FPx, Fx, FmF));

  loc(PFx) = loc(PFmF) + t*right = loc(FPx) + s*up;

  drop(PFx, PmF, Px, ox, mF, PFmF, FPmF, Fx, FmF, FPx);

  mor(PmF, Px)("P(\fold f)", top);
  mor(Px, ox)("a", rt);
  mor(PmF, mF)("\alg", lft);
  mor(mF, ox)("\fold f", bot);

  mor(PFmF, PmF)("P\roll", llft);
  mor(PFmF, FPmF)("\strength", llft);
  mor(FPmF, FmF)("F\alg", lft);
  mor(FmF, Fx)("F(\fold f)", bot);

  mor(Fx, ox)("f", urt);

  mor(FPmF, FPx)("FP(\fold f)", top);
  mor(FPx, Fx)("Fa", rt);

  mor(FmF, mF)("\roll", ulft);
  mor(PFmF, PFx)("PF(\fold f)", top);
  mor(PFx, FPx)("\strength", rt);
  mor(PFx, Px)("Pf", lrt);

  commute_gen(FPmF, FPx, Fx, FmF)("\text{IH}");
  commute_explained(PFmF, FmF, mF)("$\alg$-def");
  commute_explained(PmF, PFmF, PFx, Px)("$P(\fold f$-def$)$");
  commute_explained(PFmF, FPmF, PFx, FPx)("$\strength$-nat");
  commute_explained(PFx, Px, ox, Fx)("$P$-linear\\$F$-alg");
  commute_explained(FmF, Fx, ox, mF)("$(\fold f)$-def");
endfig;

end
