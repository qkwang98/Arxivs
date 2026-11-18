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
beginfig(41)
  obj(FmF)("F\fix F");
  obj(mF )("\fix F");
  obj(FEx)("FEx");
  obj(Ex)("Ex");

  obj(EPFmF)("EPF\fix F");
  obj(EFPmF)("EFP\fix F");
  obj(EFx)("EFx");
  obj(FEPmF)("FEP\fix F");
  obj(EPmF)("EP\fix F");


  origin
    = loc(mF)
    = loc(FEx) + 10u*left + 3u*down;

  canonical_rectangle(locs(FmF, FEx, Ex, mF));

  evenly_spaced(locs(mF, EPmF, Ex));
  evenly_spaced(locs(FmF, FEPmF, FEx));
  evenly_spaced(locs(FEPmF, EFPmF, EPmF));
  z1 = .5[loc(FmF), loc(mF)];
  evenly_spaced(z1, locs(EPFmF, EFPmF, EFx));
  drop(FmF, FEx, Ex, mF, EPmF, FEPmF, EFPmF, EFx, EPFmF);

  mor(FmF, mF)("\roll", lft);
  mor(mF, EPmF)("\eta", bot);
  mor(EPmF, Ex)("Ek", bot);
  mor(FmF, FEPmF)("F\eta", top);
  mor(FEPmF, FEx)("FEk", top);
  mor(FEx, Ex)("g", rt);

  mor(FmF, EPFmF)("\eta", llft);
  mor(EPFmF, EPmF)("EP\roll", llft);
  mor(EPFmF, EFPmF)("E\strength", bot);
  mor(FEPmF, EFPmF)("\costrength", lft);
  mor(EFPmF, EFx)("EFk", bot);
  mor(FEx, EFx)("\costrength",ulft);
  mor(EFx, Ex)("Ef", llft);

  commute_explained(EPFmF, mF)("$\eta$-nat");
  commute_explained(EFPmF, EPmF, EFx, Ex)("$E(*)$");
  commute_explained(FEPmF, EFx)("$\costrength$ nat");
  commute_explained(FmF, FEPmF, EPFmF)("Strength-Costrength\\lemma");
  commute_gen(FEx, EFx, Ex)("\defines");
endfig;

end
