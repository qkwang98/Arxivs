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
beginfig(31)
  obj(FEx)("FEx");
  obj(EFx)("EFx");
  obj(EPFEx)("EPFEx");
  obj(EFPEx)("EFPEx");

  origin
    = loc(EFx)
    = loc(EPFEx) + 2u*left + u*down;

  canonical_rectangle(locs(FEx, EPFEx, EFPEx, EFx));
  drop(FEx, EPFEx, EFPEx, EFx);

  mor(FEx, EFx)("\costrength", lft);
  mor(FEx, EPFEx)("\eta", top);
  mor(EPFEx,EFPEx)("E\strength", rt);
  mor(EFPEx, EFx)("EF\epsilon", bot);

  commute_gen(FEx, EPFEx, EFPEx, EFx)("\definedby");
endfig;

end
