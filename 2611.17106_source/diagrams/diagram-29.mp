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
beginfig(29)
  obj(A)( "\carrier\A");
  obj(Bl)("\carrier\B");
  obj(Bm)("\carrier\B");
  obj(Br)("\carrier\B");
  obj(Cl)("\carrier\C");
  obj(Cr)("\carrier\C");

  origin
    = loc(Cl)
    = loc(Br) + 2u*left + u*down;

  canonical_rectangle(locs(Bl, Br, Cr, Cl));
  evenly_spaced(locs(Bl,A ,Br));
  evenly_spaced(locs(Cl,Bm,Cr));
  drop(A, Bl, Bm, Br, Cl, Cr);

  mor(A, Bl)("t", bot);
  mor(Br, A)("g", bot);
  mor(Bm,Cl)("s", top);
  mor(Cr,Bm)("q", top);
  mor(Cl,Bl)("q", lft);
  mor(Bm, A)("f", rt);
  mor(Cr,Br)("q", rt);

  gen_curved_equals_mor(-45)(Br,Bl)("",) top_eq;
  gen_curved_equals_mor( 45)(Cr,Cl)("",) bot_eq;


  commute(Bl,A,Bm,Cl);
  commute(A,Br,Cr,Bm);
  commute(A,top_eq);
  commute(Bm,bot_eq);

endfig;

end
