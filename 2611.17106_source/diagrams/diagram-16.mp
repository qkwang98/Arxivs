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
beginfig(16)
  obj(GG_FX)("(\carrier\G \times \carrier\G)\times F\X");
  obj(G_GFX)("\carrier\G \times(\carrier\G \times F\X)");
  obj(G_FGX)("\carrier\G \times F(\carrier\G \times \X)");
  obj(FG_GX)("F(\carrier\G \times (\carrier\G \times \X))");
  obj(FGX)("F(\carrier\G \times \X)");
  obj(GFX)("\carrier\G \times F\X");
  obj(FGG_X)("F((\carrier\G\times\carrier\G)\times\X)");

  origin
    = z1
    = loc(G_GFX)+ u*left
    = loc(GG_FX) + 1.5u*right + u*down;

  evenly_spaced(z1, loc(G_GFX), z2, z3, loc(G_FGX));
  2(0, ypart(loc(GG_FX)) - y1)
    = loc(GFX) - loc(G_GFX)
    = loc(FGX) - loc(G_FGX);

  (loc(G_GFX) - loc(GG_FX)) reflectedabout (origin, right) = loc(FG_GX) - loc(G_FGX)  ;

  evenly_spaced(locs(GFX, FGG_X, G_FGX));

  drop( GG_FX
      , G_GFX
      , G_FGX
      , FG_GX
      , FGX
      , GFX
      , FGG_X
      );

  mor(GG_FX, G_GFX)("\assoc", llft);
  mor(G_GFX, G_FGX)("\strength", bot);
  mor(G_FGX, FG_GX)("\strength", lrt);
  mor(FG_GX, FGX)("F\mapmul", urt);

  mor(GG_FX, GFX)("(\mul)\times \id", ulft);
  mor(GFX, FGX)("\strength", top);

  mor(GG_FX, FGG_X)("\strength_{\carrier\G\times\carrier\G}", bot);
  mor(FGG_X, FG_GX)("F\assoc", bot);
  mor(FGG_X, FGX)("F((\mul)\times\id)", ulft);

  commute_explained(G_GFX, FGG_X, FGG_X, G_FGX)("strength\\pentagon");
  commute_explained(GFX, FGG_X, GG_FX)("strength\\nat");
  commute_explained(FGG_X, FGX, FG_GX)("products");
endfig;

end
