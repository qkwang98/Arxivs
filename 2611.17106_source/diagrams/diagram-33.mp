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
beginfig(33)
  obj(Fx)("Fx");
  obj(FEPx)("FEPx");
  obj(EFPx)("EFPx");
  obj(EPFx)("EPFx");

  origin
    = loc(EPFx)
    = loc(FEPx) + 3u*left + u*down;

  canonical_rectangle(locs(Fx, FEPx, EFPx, EPFx));

  drop(Fx, FEPx, EFPx, EPFx);

  mor(Fx, FEPx)("F\eta", top);
  mor(FEPx, EFPx)("\costrength", rt);
  mor(Fx, EPFx)("\eta", lft);
  mor(EPFx, EFPx)("E\strength", bot);

  commute(Fx, FEPx, EFPx, EPFx);
endfig;

end
