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
beginfig(23)
  obj(mFsrc )("\fix F");
  obj(mFtgt )("\fix F");
  obj(FmFsrc)("F\fix F");
  obj(FmFtgt)("F\fix F");
  obj(FGmF  )("F(\carrier\G\times \fix F)");
  obj(GFmF  )("\carrier\G \times F\fix F");
  obj(GmF   )("\carrier\G \times \fix F");

  origin
    = z0
    = z2 + 8u*left + 4u*down;

  canonical_rectangle(z0, z1, z2, z3);
  vertically_spaced(z0, locs(mFsrc, FGmF, GFmF), z3);
  xpart(loc(mFsrc)) = x0;
  xpart(loc(mFtgt)) = x1;
  yaligned(loc(mFtgt), loc(mFsrc));

  evenly_spaced(locs(mFsrc, FmFsrc, FmFtgt, mFtgt));
  z4 = .5[loc(FmFsrc), loc(FmFtgt)];
  loc(GmF) = .5[z2,z3];

  xaligned(loc(FGmF), loc(GmF));
  evenly_spaced(loc(FmFsrc), z5, loc(GFmF), z3);

  drop( mFsrc
      , mFtgt
      , FmFsrc
      , FmFtgt
      , FGmF
      , GFmF
      , GmF
      );

  explicit_equals_mor(mFsrc, mFtgt)
    (loc(mFsrc) -- z0 -- z1 -- loc(mFtgt))
    ("",top);
  explicit_mor(mFsrc, GmF)
    (loc(mFsrc) -- z3 -- loc(GmF))
    ("\pair\unit\id", urt);
  explicit_mor(GmF, mFtgt)
    ( loc(GmF)--z2--loc(mFtgt))
    ("(\act)", ulft);

  mor(FmFsrc, mFsrc)("\roll", top);
  mor(FmFtgt, mFtgt)("\roll", top);
  explicit_mor(FmFsrc, FGmF)
    (loc(FmFsrc)--(xpart(loc(FmFsrc)), ypart(loc(FGmF)))--loc(FGmF))
    ("F\pair\unit\id",lrt);
  explicit_mor(FGmF, FmFtgt)
    (loc(FGmF)--(xpart(loc(FmFtgt)), ypart(loc(FGmF)))--loc(FmFtgt))
    ("F(\act)",llft);

  equals_mor(FmFsrc, FmFtgt)("",);
  mor(FmFsrc, GFmF)("\pair\unit\id", llft);
  mor(GFmF, GmF)("\id\times\roll", ulft);
  mor(GFmF, FGmF)("\gstrength", urt);

  commute_gen(FmFsrc, FmFtgt, FGmF)("\text{IH}");
  commute_explained(GFmF, mFsrc)("products");
  commute_explained(FmFsrc, FGmF, GFmF, GFmF)("strength\\axiom");
  commute_explained(mFtgt, GmF)("$(\act)$-def");
endfig;

end
