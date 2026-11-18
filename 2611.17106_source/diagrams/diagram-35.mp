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
beginfig(35)
  obj(Fx)("Fx");
  obj(FEPx)("FEPx");
  obj(EFPx)("EFPx");
  obj(EPFx)("EPFx");

  origin
    = loc(EPFx)
    = loc(FEPx) + 6u*left + 3u*down;

  obj(EPFEPx)("EPFEPx");
  obj(EFPEPx)("EFPEPx");
  obj(EFPy)("EFPx");


  canonical_rectangle(locs(Fx, FEPx, EFPx, EPFx));
  evenly_spaced(loc(Fx), z2, loc(EPFEPx), z1, loc(EFPEPx), z3, loc(EFPx));
  evenly_spaced(loc(EPFx), loc(EFPy), loc(EFPx));

  drop(Fx, FEPx, EFPx, EPFx,EPFEPx, EFPEPx, EFPy);

  mor(Fx, FEPx)("F\eta", top);
  mor(FEPx, EFPx)("\costrength", rt);
  mor(Fx, EPFx)("\eta", lft);
  var_curved_mor(EPFx, EFPx)("E\strength", bot) botStr;

  mor(EPFx, EPFEPx)("EPF\eta", ulft);
  mor(FEPx,  EPFEPx)("\eta", ulft);
  mor(EPFEPx, EFPEPx)("E\strength", urt);
  mor(EPFx, EFPy)("E\strength", bot);
  mor(EFPy, EFPEPx)("EFP\eta", ulft);
  equals_mor(EFPy, EFPx)("",);
  mor(EFPEPx, EFPx)("EF\epsilon", urt);

  commute_explained(Fx, EPFEPx)("$\eta$-nat");
  commute_explained(EPFEPx, EFPEPx, EFPy, EPFx, EPFx)("$E(\strength$-nat$)$");
  commute_explained(EFPEPx, EFPx, EFPy)("$EF($adjunction$)$");
  commute_gen(EFPEPx, FEPx)("\defines");
  commute(EFPy, botStr);
endfig;

end
