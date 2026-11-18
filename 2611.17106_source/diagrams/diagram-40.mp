input okdefs;
input commutative_diagrams;

TEXPRE(
  ""                           & char(10) &
  "%&latex"                    & char(10) &
  "\PassOptionsToPackage{usenames,dvipsnames,svgnames,table}{xcolor}" &
                                 char(10) &
  "\documentclass[40]{article}"    & char(10) &
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
beginfig(40)
  obj(PFmF)("PF\fix F");
  obj(FPmF)("FP\fix F");
  obj(PmF )("P \fix F");
  obj(Fx)("Fx");
  obj(Ox)(" x");

  origin
    = loc(PmF)
    = loc(Fx) + 5u*left + u*down;

  canonical_rectangle(locs(PFmF, Fx, Ox, PmF));
  evenly_spaced(locs(PFmF, FPmF, Fx));
  drop(PFmF, Fx, Ox, PmF, FPmF);

  mor(PFmF, PmF)("P\roll", lft);
  dashed_mor(PmF, Ox)("k", bot);
  mor(PFmF, FPmF)("\strength", top);
  mor(FPmF, Fx)("Fk", top);
  mor(Fx, Ox)("f", rt);

  commute_explained(PFmF, Fx, Ox, PmF)("($*$)");

endfig;

end
