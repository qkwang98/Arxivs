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
  "\newcommand{\uplambda}{\mathord{\text{\usefont{U}{fsy}{m}{n}{\char `l}}}}"
                               & char(10) &
  "\usepackage{libertine}"     & char(10) &
  "\input{defs}"               & char(10) &
  "\begin{document}"           & char(10) &
  ""
  );

outputtemplate := "diagram-%2c.mps";
beginfig(30)
  obj(FamGl)("\Fam_{\carrier\Ctx}");
  obj(FamGr)("\Fam_{\carrier\Ctx}");
  obj(ActGm)("\Action\G_{\Ctx}");


  origin
    = loc(FamGl)
    = loc(ActGm) + 4u*left;

  loc(FamGl)
    = z1 + u*up;
  loc(FamGr)
    = z3 + u*down;

  canonical_rectangle(z1, z2, z3, z4);


  evenly_spaced(locs(FamGl, ActGm, FamGr));
  drop(FamGl, ActGm, FamGr);

  curved_mor(FamGl, ActGm)("\DPair\mg\G{\mg\act-}",top);
  curved_mor(FamGr, ActGm)("\DFun\mg\G{\inv\mg\act-}",bot);
  curved_mor(ActGm, FamGr)("\carrier-",top);
  curved_mor(ActGm, FamGl)("\carrier-",bot);

  explicit_mor(FamGl, FamGr)
    (loc(FamGl)--z4--z3--loc(FamGr))
    ("P\definedby \gast", top) monad;
  explicit_mor(FamGr, FamGl)
    (loc(FamGl)--z1--z2--loc(FamGr))
    ("E\definedby \lollybox", bot) comonad;

  commute_gen(FamGl, ActGm)("\bot");
  commute_gen(FamGr, ActGm)("\bot");

  commute_gen(monad, ActGm)("\definedby");
  commute_gen(comonad, ActGm)("\definedby");
endfig;

end
