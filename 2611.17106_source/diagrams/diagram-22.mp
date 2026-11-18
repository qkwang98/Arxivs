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
beginfig(22)
  obj(GFA)("\carrier\G\times \carrier F\carrier\A");
  obj(GA)("\carrier\G\times \carrier\A");
  obj(A)("\carrier\A");
  obj(FA)("\carrier F\carrier\A");
  obj(FGA)("\carrier F(\carrier\G\times \carrier\A)");

  origin
    = loc(GA)
    = loc(FA) + 5u*left + 1u*down;

  canonical_rectangle(locs(GFA, FA, A, GA));
  evenly_spaced(locs(GFA, FGA, FA));
  drop(GFA, FA, A, GA, FGA);

  commute(GFA, FA, A, GA);

  mor(GFA, GA)("\id\times f", lft);
  mor(GA, A)("(\act)", bot);
  mor(GFA, FGA)("\gstrength", top);
  mor(FGA, FA)("F(\act)", top);
  mor(FA, A)("f", rt);

endfig;

end
