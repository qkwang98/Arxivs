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
beginfig(52)
  obj(CA)("(\Canon\canoniser)\A");
  obj(FA)("                  F\A");
  obj( A)("                   \A");
  obj(CB)("(\Canon\canoniser)\B");
  obj(FB)("                  F\B");
  obj( B)("                   \B");

  origin
    = loc(CB)
    = loc(FA) + 2u*left + u*down;

  canonical_rectangle(locs(CA, FA, FB, CB));
  evenly_spaced(locs(CA, FA, A));
  evenly_spaced(locs(CB, FB, B));

  drop(CA, FA, A, CB, FB, B);

  mor(CA, CB)("(\Canon\canoniser)h", lft);
  mor(FA, FB)("Fh", lft);
  mor(A, B)("h", rt);

  monic(CA, FA)("", top);
  monic(CB, FB)("", top);
  mor(FA, A)("f", top);
  mor(FB, B)("g", bot);

  commute_explained(CA, CB, FA, FB)("naturality");
  commute_gen(A, B, FA, FB)("(**)");
endfig;

end
