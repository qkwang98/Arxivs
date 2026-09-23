# The block B2 of 3.O7(3) at 2.

if LoadPackage("ctbllib") <> true then
  Error("The CTblLib package is required.");
fi;

Check := function(ok,msg) if not ok then Error(msg); fi; end;;
Val2 := function(n)
local v;
v:=0;
while n mod 2=0 do n:=n/2; v:=v+1; od;
return v;
end;;

Main := function()
local u,a,bu,blocks,b2,dec,cartan,degrees,heights,zpos,ratios,i,j,
      fusion,auts,allFibres,target,fibre,candidates,p,good,outer,
      orders,pregPositions,pregImage,action,transformed,hits,brauerPerm,
      blockAction,imageSet,blockPerm;

u:=CharacterTable("3.O7(3)");;
a:=CharacterTable("3.O7(3).2");;
bu:=BrauerTable(u,2);;
blocks:=BlocksInfo(bu);;
Check(Length(blocks)=9,"The covering group should have nine 2-blocks.");;
b2:=blocks[2];;
Check(b2.defect=3,"The defect exponent of B2 should be 3.");;
Check(b2.modchars=[13,14],"The Brauer labels of B2 should be [13,14].");;
Check(b2.ordchars=[36,37,47,52,53],
      "The ordinary labels of B2 should be [36,37,47,52,53].");;

dec:=DecompositionMatrix(bu);;
cartan:=(TransposedMat(dec)*dec){b2.modchars}{b2.modchars};;
degrees:=List(b2.ordchars,j->Irr(u)[j][1]);;
heights:=List(degrees,d->Val2(d)-(Val2(Size(u))-b2.defect));;
Check(degrees=[5824,5824,11648,17472,17472],
      "The ordinary character degrees of B2 are unexpected.");;
Check(heights=[0,0,1,0,0],"The character heights of B2 are unexpected.");;
Check(cartan=[[4,2],[2,3]],"The Cartan matrix of B2 should be [[4,2],[2,3]].");;

zpos:=ClassPositionsOfCenter(u);;
ratios:=List(zpos,k->Irr(bu)[b2.modchars[1]][k]/
                     Irr(bu)[b2.modchars[1]][1]);;
Check(ratios=[1,1,1],"The central character of B2 should be trivial.");;
for j in b2.modchars do
  Check(List(zpos,k->Irr(bu)[j][k]/Irr(bu)[j][1])=ratios,
        "The central character is not constant on B2.");;
od;

fusion:=GetFusionMap(u,a);;
auts:=AutomorphismsOfTable(u);;
allFibres:=[];;
for target in Set(fusion) do
  fibre:=Filtered([1..Length(fusion)],x->fusion[x]=target);;
  Check(Length(fibre)<=2,
        "A fusion fibre in the overgroup contains more than two classes.");;
  Add(allFibres,fibre);;
od;
candidates:=[];;
for p in Elements(auts) do
  good:=true;;
  for fibre in allFibres do
    if Length(fibre)=1 then
      if fibre[1]^p<>fibre[1] then good:=false; fi;
    else
      if fibre[1]^p<>fibre[2] or fibre[2]^p<>fibre[1] then
        good:=false;
      fi;
    fi;
  od;
  if good then Add(candidates,p); fi;
od;
Check(Length(candidates)=1,"The fusion does not determine a unique outer action.");;
outer:=candidates[1];;

orders:=OrdersClassRepresentatives(u);;
pregPositions:=Filtered([1..Length(orders)],i->orders[i] mod 2<>0);;
pregImage:=List(pregPositions,i->Position(pregPositions,i^outer));;
Check(not fail in pregImage,
      "The outer action does not preserve the 2-regular classes.");;
action:=[];;
for j in [1..Length(Irr(bu))] do
  transformed:=List([1..Length(pregPositions)],
                    i->Irr(bu)[j][pregImage[i]]);;
  hits:=Filtered([1..Length(Irr(bu))],
                 k->transformed=List(Irr(bu)[k],x->x));;
  Check(Length(hits)=1,
        "A Brauer character does not have a unique image under the outer action.");;
  Add(action,hits[1]);;
od;
brauerPerm:=PermList(action);;
Check(brauerPerm<>fail,"The action on Brauer characters is not a permutation.");;

blockAction:=[];;
for i in [1..Length(blocks)] do
  imageSet:=Set(List(blocks[i].modchars,j->j^brauerPerm));;
  hits:=Filtered([1..Length(blocks)],
                 k->Set(blocks[k].modchars)=imageSet);;
  Check(Length(hits)=1,
        "A block does not have a unique image under the outer action.");;
  Add(blockAction,hits[1]);;
od;
blockPerm:=PermList(blockAction);;
Check(blockPerm<>fail,"The action on blocks is not a permutation.");;
Check(blockAction[2]=2,"The outer automorphism does not stabilise B2.");;
Check(List(b2.modchars,j->j^brauerPerm)=[13,14],
      "The outer automorphism does not fix IBr(B2) pointwise.");;

Print("GAP_VERSION=",GAPInfo.Version,"\n");;
Print("CTBLLIB_VERSION=",PackageInfo("ctbllib")[1].Version,"\n");;
Print("X_ID=",Identifier(u),"\n");;
Print("X_ORDER=",Size(u),"\n");;
Print("B2_DEFECT_EXPONENT=",b2.defect,"\n");;
Print("B2_DEFECT_ORDER=",2^b2.defect,"\n");;
Print("B2_K=",Length(b2.ordchars),"\n");;
Print("B2_L=",Length(b2.modchars),"\n");;
Print("B2_ORDINARY_LABELS=",b2.ordchars,"\n");;
Print("B2_IBR_LABELS=",b2.modchars,"\n");;
Print("B2_ORDINARY_DEGREES=",degrees,"\n");;
Print("B2_HEIGHTS=",heights,"\n");;
Print("B2_DECOMPOSITION=",
      List(b2.ordchars,j->dec[j]{b2.modchars}),"\n");;
Print("B2_CARTAN=",cartan,"\n");;
Print("B2_CENTRAL_RATIOS=",ratios,"\n");;
Print("OUTER_BRAUER_ACTION=",brauerPerm,"\n");;
Print("OUTER_BLOCK_ACTION=",blockPerm,"\n");;
Print("B2_OUTER_IBR_IMAGE=",List(b2.modchars,j->j^brauerPerm),"\n");;
Print("Block B2 has the stated decomposition data and outer action.\n");;
end;;

Main();;
QUIT_GAP(0);
