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
beginfig(25)
  obj(GG_mF  )("(\carrier\G \times\carrier\G)\times\fix F");
  obj(GG_FmF )("(\carrier\G \times\carrier\G)\times F\fix F");
  obj(FGG_mF )("F((\carrier\G \times\carrier\G)\times \fix F)");
  obj(FmF    )("F\fix F");
  obj(mF     )("\fix F");
  obj(FGmFbot)("F(\carrier\G \times \fix F)");
  obj(FGmFtop)("F(\carrier\G \times \fix F)");
  obj(FG_GmF )("F(\carrier\G \times (\carrier\G \times \fix F))");
  obj(GFGmF  )("\carrier\G \times F(\carrier\G \times \fix F)");
  obj(G_GFmF )("\carrier\G \times (\carrier\G \times F\fix F)");
  obj(GFmFtop)("\carrier\G\times F\fix F");
  obj(GFmFbot)("\carrier\G\times F\fix F");
  obj(GmFtop )("\carrier\G\times \fix F");
  obj(GmFbot )("\carrier\G\times \fix F");
  obj(G_GmF  )("\carrier\G \times (\carrier\G \times \fix F)");

  origin
    = z0
    = z2 + 9.5u*left + 6u*down;

  canonical_rectangle(z0, z1, z2, loc(G_GmF));
  evenly_spaced(loc(G_GmF), z3, z4, loc(GG_mF), z5, z6, z0);
  loc(GmFbot) = .75[z0,z1];
  loc(mF) = .2[z1,z2];
  evenly_spaced(locs(GG_mF, GG_FmF, FGG_mF, FmF, mF));

  evenly_spaced(locs(FGG_mF, G_GFmF, G_GmF));
  evenly_spaced(loc(G_GmF), loc(GmFtop), z2);

  evenly_spaced(locs(FGG_mF, FGmFbot, GmFbot));
  evenly_spaced(loc(FGmFbot), loc(GFmFbot), z0);

  evenly_spaced(locs(G_GFmF, GFGmF, GFmFtop), z2);
  evenly_spaced(locs(GFGmF, FG_GmF, FGG_mF));
  evenly_spaced(locs(GFmFtop, FGmFtop, FmF));

  drop( GG_mF
      , GG_FmF
      , FGG_mF
      , FmF
      , mF
      , FGmFbot
      , FGmFtop
      , FG_GmF
      , GFGmF
      , G_GFmF
      , GFmFtop
      , GFmFbot
      , GmFtop
      , GmFbot
      , G_GmF
      );

  explicit_mor(GG_mF, GmFbot)
    (loc(GG_mF) -- (xpart(loc(GG_mF)), ypart(loc(GmFbot)))  -- loc(GmFbot))
    ("\scriptstyle(\mul)\times\id", bot);
  explicit_mor(GmFbot, mF)
    ( loc(GmFbot) -- (xpart(loc(mF)), ypart(loc(GmFbot))) -- loc(mF))
    ("(\act)",bot);

  mor(GG_mF, G_GmF)("\assoc", lft);
  mor(G_GmF, GmFtop)("\scriptstyle\id\times(\act)", top);
  explicit_mor(GmFtop, mF)
    (loc(GmFtop) -- (xpart(loc(mF)), ypart(loc(GmFtop))) -- loc(mF))
    ("\scriptstyle(\act)", rt)  rt_exp;

  mor(G_GFmF, G_GmF)("\scriptstyle\id\times(\id\times\roll)", rt);
  var_curved_mor(GG_FmF, GG_mF)("\scriptstyle(\id\times\id)\times\roll", urt);
  curved_mor(GG_FmF, FGG_mF)("\scriptstyle\strength_2", urt);
  gen_curved_mor(-90)(GG_FmF, G_GFmF)("\assoc",rt);
  explicit_mor(FGG_mF, FGmFbot)
    (loc(FGG_mF)+.5u*left -- (xpart(loc(FGG_mF)+.5u*left), ypart(loc(FGmFbot)))
        -- loc(FGmFbot))
    ("\scriptstyle F((\mul)\times\id)",lft);

  mor(GFmFbot, FGmFbot)("\scriptstyle\strength",lrt);
  mor(GFmFbot, GmFbot )("\scriptstyle\id\times\roll",urt);

  explicit_mor(FGmFbot, FmF)
    (loc(FGmFbot) -- (xpart(loc(FmF)), ypart(loc(FGmFbot))) -- loc(FmF))
    ("(\act)", rt);

  mor(FmF, mF)("\roll", urt);

  mor(GG_FmF, GFmFbot)("(\mul)\times\id", llft);

  var_curved_mor(FGG_mF, FG_GmF)("\scriptstyle F\assoc", rt);
  mor(GFGmF, FG_GmF)("\scriptstyle\strength", rt);
  var_curved_mor(FG_GmF, FGmFtop)("F(\id\times(\act))",bot);
  curved_mor(GFGmF, GFmFtop)("\id\times F(\act)", ulft);

  curved_mor(FGmFtop, FmF)("\scriptstyle F(\act)", rt);
  mor(GFmFtop, FGmFtop)("\scriptstyle \strength", rt);
  mor(GFmFtop, GmFtop)("\scriptstyle\id\times\roll", urt);

  mor(G_GFmF, GFGmF)("\scriptstyle\id\times\strength", ulft);

  commute_explained(GFmFbot, GG_mF)("functoriality");
  commute_explained(GG_mF, G_GFmF, G_GmF)("$\assoc$ nat");
  commute_explained(GFGmF, GmFtop, G_GmF)("$\carrier\G\times(\act)$-def");
  commute_explained(GFGmF, FGmFtop, GFmFtop)("strength\\nat");
  commute_explained(FGmFtop, mF, rt_exp)("$(\act)$-def");
  commute_explained(G_GFmF, FG_GmF, GFGmF)("$\strength_2$\\def");
  commute_gen(FGG_mF, FmF)("\text{IH}");
  commute_explained(GG_FmF, FGG_mF, GFmFbot)("second\\strength\\axiom");
  commute_explained(GmFbot, mF)("$(\act)$-def");
endfig;

end
