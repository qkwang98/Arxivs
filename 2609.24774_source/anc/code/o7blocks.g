# The 2-blocks of 3.O7(3) and their outer action.

if LoadPackage("ctbllib") <> true then
  Error("The CTblLib package is required.");
fi;

Check := function(ok,msg) if not ok then Error(msg); fi; end;;
Main := function()
local u, a, bu, ba, ublocks, ablocks, i, j, tree, zpos, ratios,
      fusion, auts, allFibres, target, fibre, candidates, p, good,
      outer, orders, pregPositions, pregImage, action, transformed,
      hits, brauerPerm, blockAction, imageSet, blockPerm, dec, subdec;

u := CharacterTable("3.O7(3)");;
a := CharacterTable("3.O7(3).2");;
bu := BrauerTable(u,2);;
ba := BrauerTable(a,2);;
ublocks := BlocksInfo(bu);;
ablocks := BlocksInfo(ba);;

Check(Length(ublocks)=9,
      "The character table of 3.O7(3) should have nine 2-blocks.");;
dec := DecompositionMatrix(bu);;

Print("GAP_VERSION=",GAPInfo.Version,"\n");;
Print("CTBLLIB_VERSION=",PackageInfo("ctbllib")[1].Version,"\n");;
Print("U_ID=",Identifier(u),"\n");;
Print("U_ORDER=",Size(u),"\n");;
Print("U_BLOCK_COUNT=",Length(ublocks),"\n");;
for i in [1..Length(ublocks)] do
  tree := IsBound(ublocks[i].brauertree);;
  Print("U_BLOCK_",i,"_DEFECT=",ublocks[i].defect,
        ";IBR=",ublocks[i].modchars,
        ";ORD=",ublocks[i].ordchars,
        ";BRAUER_TREE_STORED=",tree,"\n");;
  subdec := List(ublocks[i].ordchars,
                 j -> dec[j]{ublocks[i].modchars});;
  Print("U_BLOCK_",i,"_DECOMPOSITION_SUBMATRIX=",subdec,"\n");;
od;

zpos := ClassPositionsOfCenter(u);;
Print("U_CENTRE_CLASS_POSITIONS=",zpos,"\n");;
for i in [1..Length(ublocks)] do
  j:=ublocks[i].modchars[1];;
  ratios:=List(zpos,k->Irr(bu)[j][k]/Irr(bu)[j][1]);;
  for j in ublocks[i].modchars do
    Check(List(zpos,k->Irr(bu)[j][k]/Irr(bu)[j][1])=ratios,
          "The central character is not constant on the block.");;
  od;
  Print("U_BLOCK_",i,"_CENTRAL_RATIOS=",ratios,"\n");;
od;

fusion:=GetFusionMap(u,a);;
auts:=AutomorphismsOfTable(u);;
allFibres:=[];;
for target in Set(fusion) do
  fibre:=Filtered([1..Length(fusion)],x->fusion[x]=target);;
  Check(Length(fibre)<=2,"A fusion fibre contains more than two classes.");;
  Add(allFibres,fibre);;
od;
candidates:=[];;
for p in Elements(auts) do
  good:=true;;
  for fibre in allFibres do
    if Length(fibre)=1 then
      if fibre[1]^p<>fibre[1] then good:=false; fi;
    else
      if fibre[1]^p<>fibre[2] or fibre[2]^p<>fibre[1] then good:=false; fi;
    fi;
  od;
  if good then Add(candidates,p); fi;
od;
Check(Length(candidates)=1,
      "The fusion does not determine a unique outer action on U.");;
outer:=candidates[1];;
orders:=OrdersClassRepresentatives(u);;
pregPositions:=Filtered([1..Length(orders)],i->orders[i] mod 2<>0);;
pregImage:=List(pregPositions,i->Position(pregPositions,i^outer));;
Check(not fail in pregImage,
      "The outer action does not preserve the 2-regular classes.");;
action:=[];;
for j in [1..Length(Irr(bu))] do
  transformed:=List([1..Length(pregPositions)],i->Irr(bu)[j][pregImage[i]]);;
  hits:=Filtered([1..Length(Irr(bu))],k->transformed=List(Irr(bu)[k],x->x));;
  Check(Length(hits)=1,
        "A Brauer character does not have a unique image under the outer action.");;
  Add(action,hits[1]);;
od;
Print("U_BRAUER_OUTER_ACTION_LIST_RAW=",action,"\n");;
brauerPerm:=PermList(action);;
Check(brauerPerm<>fail,"The action on Brauer characters is not a permutation.");;
Print("U_TABLE_AUTOMORPHISM_GROUP_ORDER=",Size(auts),"\n");;
Print("U_FUSION_FORCED_OUTER_CLASS_ACTION=",outer,"\n");;
Print("U_BRAUER_OUTER_ACTION=",brauerPerm,"\n");;

blockAction:=[];;
for i in [1..Length(ublocks)] do
  imageSet:=Set(List(ublocks[i].modchars,j->j^brauerPerm));;
  hits:=Filtered([1..Length(ublocks)],k->Set(ublocks[k].modchars)=imageSet);;
  Check(Length(hits)=1,
        "A block does not have a unique image under the outer action.");;
  Add(blockAction,hits[1]);;
od;
blockPerm:=PermList(blockAction);;
Check(blockPerm<>fail,"The action on blocks is not a permutation.");;
Print("U_BLOCK_OUTER_ACTION=",blockPerm,"\n");;
Print("U_BLOCK_OUTER_ACTION_LIST=",blockAction,"\n");;

Print("A_ID=",Identifier(a),"\n");;
Print("A_BLOCK_COUNT=",Length(ablocks),"\n");;
for i in [1..Length(ablocks)] do
  Print("A_BLOCK_",i,"_DEFECT=",ablocks[i].defect,
        ";IBR=",ablocks[i].modchars,
        ";ORD=",ablocks[i].ordchars,"\n");;
od;
Print("The nine blocks and their outer action have the stated form.\n");;
end;;

Main();;
QUIT_GAP(0);
