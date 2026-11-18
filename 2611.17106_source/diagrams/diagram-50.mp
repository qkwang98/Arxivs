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
  "\usepackage{libertine}"     & char(10) &
  "\input{defs}"               & char(10) &
  "\begin{document}"           & char(10) &
  ""
  );

outputtemplate := "diagram-%2c.mps";
beginfig(50)
  obj(GFA)("\carrier\G\times \carrier F\fix\carrier F");
  obj(GA)("\carrier\G\times \fix\carrier F");
  obj(A)("\fix\carrier F");
  obj(FA)("\carrier F\fix\carrier F");
  obj(FGA)("\carrier F(\carrier\G\times \fix\carrier F)");

  origin
    = loc(GA)
    = loc(FA) + 5u*left + 1u*down;

  canonical_rectangle(locs(GFA, FA, A, GA));
  evenly_spaced(locs(GFA, FGA, FA));
  drop(GFA, FA, A, GA, FGA);

  commute(GFA, FA, A, GA);

  mor(GFA, GA)("\id\times \roll", lft);
  mor(GA, A)("(\act[\fix F])", bot);
  mor(GFA, FGA)("\gstrength", top);
  mor(FGA, FA)("F(\act[\fix F])", top);
  mor(FA, A)("\roll", rt);

endfig;

end
