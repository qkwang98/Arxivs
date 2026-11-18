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
beginfig(26)
  obj(GmF )("\carrier\G\times\fix F");
  obj(GFmF)("\carrier\G \times F\fix F");
  obj(FGmF)("F(\carrier\G\times\fix F)");
  obj(FGA )("F(\carrier \G\times\carrier\A)");
  obj(GFA )("\carrier \G\times F\carrier\A");
  obj(FA  )("F\carrier\A");
  obj(A   )("\carrier\A");
  obj(mF  )("\fix F");
  obj(GA  )("\carrier\G \times \carrier\A");
  obj(FmF )("F\fix F");

  origin
    = loc(GmF) + 2u*down
    = loc(mF)  + 5u*left;

  loc(A) = loc(GmF) reflectedabout(loc(mF), loc(mF) + up);
  loc(GA) = loc(mF) reflectedabout(loc(GmF), loc(GmF) + right);

  evenly_spaced(locs(mF, FmF, FGmF, FGA, GA));
  evenly_spaced(locs(GmF, GFmF, FGmF, FA, A));
  loc(GFA) = (xpart(loc(GFmF)), ypart(loc(FGA)));
  drop( GFA
      , GmF
      , GFmF
      , FGmF
      , FGA
      , FA
      , A
      , mF
      , GA
      , FmF
      );

  explicit_mor(GmF, mF)
    (loc(GmF) -- (xpart(loc(GmF)), ypart(loc(mF))) -- loc(mF))
    ("\scriptstyle(\act)", bot);

  explicit_mor(mF, A)
    (loc(mF) -- (xpart(loc(A)), ypart(loc(mF))) -- loc(A))
    ("\scriptstyle\fold f", bot) lr_exp;

  explicit_mor(GmF, GA)
    (loc(GmF) -- (xpart(loc(GmF)), ypart(loc(GA))) -- loc(GA))
    ("\scriptstyle\id \times \fold f", top) ul_exp;

  explicit_mor(FA, A)
    (loc(FA) -- (xpart(loc(A)), ypart(loc(FA))) -- loc(A))
    ("\scriptstyle(\act)", top);

  mor(GFmF, GmF)("\scriptstyle\id\times\roll", bot);
  mor(GFmF, FGmF)("\scriptstyle\strength", bot);
  mor(FGmF, FmF)("\scriptstyle F(\act)", lft);
  explicit_mor(FmF, FA)
    (loc(FmF) -- (xpart(loc(FA)), ypart(loc(FmF))) -- loc(FA))
    ("\scriptstyle F(\fold f)", bot);

  explicit_mor(GA, A)
    (loc(GA) -- (xpart(loc(A)), ypart(loc(GA))) -- loc(A))
    ("(\act)", top) ur_exp;
  mor(FGmF, FGA)("\scriptstyle F(\id\times\fold f)", rt);
  explicit_mor(FGA, FA)
    (loc(FGA) -- (xpart(loc(FA)), ypart(loc(FGA))) -- loc(FA))
    ("\scriptstyle F(\act)",top);

  mor(GFmF, GFA)("\scriptstyle\id \times F(\fold f)", lft);
  mor(GFA, FGA)("\scriptstyle\strength", top);
  mor(GFA, GA)("\scriptstyle\id\times f", ulft);
  mor(FmF, mF)("\scriptstyle\roll", lft);

  commute_explained(mF, GmF)("$(\act)$-def");
  commute_explained(A, lr_exp)("$\fold f$ def");
  commute_explained(FA, FmF)("IH");
  commute_explained(GFmF, FGA)("strength nat.");
  commute_explained(ul_exp, GmF)("$\carrier\G\times\fold f$ def");
  commute_explained(A, ur_exp)("$f$ equivariance");
endfig;

end
