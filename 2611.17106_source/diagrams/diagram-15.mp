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
  "\input{defs}"               & char(10) &
  "\usepackage{libertine}"     & char(10) &
  "\DeclareFontFamily{U}{fsy}{}" & char(10) &
  "\DeclareFontShape{U}{fsy}{m}{n}{<->s*[.9]psyr}{}" & char(10) &
  "\DeclareSymbolFont{ok@up@greek}{U}{fsy}{m}{n}" & char(10) &
  "\DeclareMathSymbol{\uplambda}{\mathord}{ok@up@greek}{`l}" & char(10) &
  "\begin{document}"           & char(10) &
  ""
  );

outputtemplate := "diagram-%2c.mps";
beginfig(15)
  obj(FX)("FX");
  obj(IFX)("\terminal \times FX");
  obj(GFX)("\carrier\G \times FX");
  obj(FIX)("F(\terminal\times X)");
  obj(FGX)("F(\carrier\G\times X)");

  origin
    = loc(GFX)
    = loc(FX) + 4u*left + 2.5u*down;

  evenly_spaced(z1, loc(IFX), z3, z4,loc(FIX), z2);
  evenly_spaced(loc(FX), z1, loc(GFX));
  evenly_spaced(loc(FX), z2, loc(FGX));
  horizontally_spaced(locs(GFX, FX, FGX));
  yaligned(loc(GFX), loc(FGX));
  drop(FX, IFX, GFX, FIX, FGX);

  mor(FX, IFX)("(\fun x\unitval)", ulft);
  mor(IFX, GFX)("(\fun x\unit)\times \id", lrt);
  gen_curved_mor(-45)(FX, GFX)("\pair\unit-", ulft) lft_curve;
  gen_curved_mor(+45)(FX, FGX)("F\pair\unit-", urt) rgt_curve;

  mor(FX, FIX)("F(\fun x\pair\star x)", urt);
  mor(FIX, FGX)("F((\fun x\unit)\times \id)", llft);
  mor(IFX, FIX)("\strength_{\terminal}", bot);
  mor(GFX, FGX)("\strength_{\carrier\G}", bot);

  commute_explained(FX, IFX, FIX)("unit\\axiom");
  commute_explained(lft_curve, IFX, GFX)("products");
  commute_explained(rgt_curve, FIX, FGX)("$F($products$)$");
  commute_explained(IFX, FIX, FGX, GFX)("strength naturality");
endfig;

end
