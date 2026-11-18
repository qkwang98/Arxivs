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
beginfig(19)
  obj(AFmF)("A\times F\fix F");
  obj(AmF)("A\times \fix F");
  obj(X)("X");
  obj(FX)("FX");
  obj(FAmF)("F(A\times \fix F)");
  obj(AFXA)("A\times F(X^A)");
  obj(AXA)("A\times X^A");
  obj(FAXA)("F(A\times X^A)");

  origin
    = loc(AmF)
    = loc(FX) + 8u*left + 3u*down;

  canonical_rectangle(locs(AFmF, FX, X, AmF));
  evenly_spaced(locs(AFmF, FAmF, FX));
  evenly_spaced(locs(AFmF, AFXA, X));
  evenly_spaced(locs(AmF, AXA, AFXA, FAXA, FX));

  drop(AXA, FAXA, AFXA, FAmF, AFmF, FX, X, AmF);
  mor(AFmF, AmF)("\id\times\roll", lft);
  mor(AmF, X)("\pfold f", bot);
  mor(AFmF, FAmF)("\strength", top);
  mor(FAmF, FX)("F(\pfold f)", top);
  mor(FX, X)("f", rt);

  mor(AFmF, AFXA)("\id\times Fk", llft);
  mor(AFXA, AXA)("\id\times h", ulft);
  mor(AmF, AXA)("\id\times k", ulft);

  mor(AFXA, FAXA)("\strength", ulft);
  mor(FAXA, FX)("F\eval", lrt);
  mor(FAmF, FAXA)("F(\id\times k)", llft);
  mor(AFXA, X)("g", urt);
  mor(AXA, X)("\eval", urt);

  commute_explained(AFmF, AFXA, AmF, AXA)("$\id\times$($*$)");
  commute_explained(AFmF, FAmF, AFXA)("strength nat.");
  commute_explained(FAmF, FAXA, FX)("$F($def$)$");
  commute_explained(AFXA, AXA, X)("currying");
  commute_explained(FAXA, X)("def");
  commute_explained(AmF, AXA, X)("def");
endfig;

end
