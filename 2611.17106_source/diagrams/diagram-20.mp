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
beginfig(20)
  obj(AFmF)("A\times F\fix F");
  obj(AmF)("A\times \fix F");
  obj(X)("X");
  obj(FX)("FX");
  obj(FAmF)("F(A\times \fix F)");

  origin
    = loc(AmF)
    = loc(FX) + 5u*left + 1u*down;

  canonical_rectangle(locs(AFmF, FX, X, AmF));
  evenly_spaced(locs(AFmF, FAmF, FX));
  drop(AFmF, FX, X, AmF, FAmF);

  commute_explained(AFmF, FX, X, AmF)("($**$)");

  mor(AFmF, AmF)("\id\times\roll", lft);
  mor(AmF, X)("p", bot);
  mor(AFmF, FAmF)("\strength", top);
  mor(FAmF, FX)("Fp", top);
  mor(FX, X)("f", rt);
endfig;

end
