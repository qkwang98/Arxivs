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
  "\newcommand{\uplambda}{\mathord{\text{\usefont{U}{fsy}{m}{n}{\char `l}}}}"
                               & char(10) &
  "\begin{document}"           & char(10) &
  ""
  );

outputtemplate := "diagram-%2c.mps";
beginfig(27)
  obj(GFmF)("\carrier G \times F\fix F");
  obj(GmF)("\carrier G \times \fix F");
  obj(FmF)("F\fix F");
  obj(mF)("\fix F");
  obj(FGmF)("F(\carrier G \times \fix F)");

  origin
    = loc(GmF)
    = loc(FmF) + 8u*left + 2u*down;

  canonical_rectangle(locs(GFmF, FmF, mF, GmF));
  evenly_spaced(locs(GFmF, FGmF, FmF));
  drop(FGmF, GFmF, FmF, mF, GmF);

  mor(GFmF, FGmF)("\strength", top);
  empty_mor(GFmF, FGmF)("\scriptstyle\fun{\pair gt}\fmap(\fun x \pair gx)t", bot);
  mor(FGmF, FmF)("F\projection_2", top);
  mor(FmF, mF)("\roll", rt);
  mor(GFmF, GmF)("\id\times\roll", lft);
  mor(GmF, mF)("\projection_2", bot);

  var_curved_mor(GFmF, FmF)("\projection_2", bot) curvey;

  commute_explained(curvey, FGmF)("products");
  commute_explained(curvey, GmF, mF)("$\projection_2$ nat");
endfig;

end
