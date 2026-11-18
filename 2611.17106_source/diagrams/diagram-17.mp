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
beginfig(17)
  obj(AFX)("A\times F(\X^A)");
  obj(FAX)("F(A\times \X^A)");
  obj(FX)("F\X");
  obj(X)("\X");

  origin
    = loc(X)
    = loc(FAX) + 3u*left + u*down;

  canonical_rectangle(locs(AFX, FAX, FX, X));
  drop(AFX, FAX, FX, X);

  mor(AFX, FAX)("\strength", top);
  mor(FAX, FX)("F\eval", rt);
  mor(FX, X)("f", bot);
  mor(AFX, X)("g", lft);

  commute_gen(AFX, FAX, FX, X)("\definedby");
endfig;

end
