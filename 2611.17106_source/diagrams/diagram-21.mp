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
beginfig(21)
  obj(AFmF)("A \times F\fix F");
  obj(AmF)("A\times \fix F");
  obj(AFXA)("A\times F(X^A)");
  obj(AXA)("A \times X^A");

  obj(FAmF)("F(A \times \fix F)");
  obj(FAXA)("F(A\times X^A)");
  obj(FX)("FX");
  obj(X)("X");

  evenly_spaced(locs(AFmF, FAXA, FX, X, AXA));
  evenly_spaced(locs(AmF, FAmF, FAXA));

  origin
    = loc(AmF)
    = loc(AFXA)  + 9u*left + 3u*down;

  canonical_rectangle(locs(AFmF, AFXA, AXA, AmF));
  drop(FAmF, AFmF, AFXA, AXA, AmF, FAXA, FX, X);

  mor(AFmF, AFXA)("\id\times Fq", top);
  mor(AFXA, AXA)("\id \times h", rt);
  mor(AFmF, AmF)("\id \times \roll", lft);
  mor(AmF, AXA)("\id \times q", bot);

  var_curved_mor(AFmF, FAmF)("\strength", urt);
  mor(FAmF, FX)("Fp", lrt);
  mor(FX, X)("f", llft);
  mor(AmF, X)("p", ulft);

  mor(FAmF, FAXA)("F(\id\times q)", ulft);
  mor(FAXA, FX)("F\eval", urt);
  mor(AFXA, FAXA)("\strength", ulft);
  mor(AFXA, X)("g", ulft);

  mor(AXA, X)("\eval", urt);

  commute_explained(AFmF, FAXA)("strength nat.");
  commute_explained(FAmF, FAXA, FX)("$F($currying$)$");
  commute_explained(FX, AFXA)("def");
  commute_explained(X, AFXA, AXA)("currying");
  commute_explained(FAmF, AmF)("($**$)");
endfig;

end
