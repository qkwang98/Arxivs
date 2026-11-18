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
beginfig(24)
  obj(GG_FX)("(\carrier\G \times \carrier\G) \times F\X");
  obj(G_GFX)("\carrier\G \times (\carrier\G \times \X)");
  obj(GFGX )("\carrier\G \times F(\carrier\G \times \X)");
  obj(FG_GX)("F(\carrier\G \times (\carrier\G \times \X))");
  obj(FGG_X)("F((\carrier\G \times \carrier\G) \times \X)");

  origin
    = loc(FGG_X)
    = loc(G_GFX) + 3u*left + 2u*down;

  canonical_rectangle(locs(FGG_X, FG_GX, G_GFX, GG_FX));
  evenly_spaced(locs(FG_GX, GFGX, G_GFX));
  drop( GG_FX
      , G_GFX
      , GFGX
      , FG_GX
      , FGG_X
      );
  mor(GG_FX, FGG_X)("\strength_2", lft);
  mor(GG_FX, G_GFX)("\assoc", top);
  mor(G_GFX, GFGX)("\id\times\strength", rt);
  mor(GFGX, FG_GX)("\strength", rt);
  mor(FG_GX, FGG_X)("F\inv\assoc", bot);

  commute_gen(GG_FX, G_GFX, FG_GX, FGG_X)("\definedby");
endfig;

end
