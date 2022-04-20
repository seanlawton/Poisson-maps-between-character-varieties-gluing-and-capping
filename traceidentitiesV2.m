(* ::Package:: *)

(* ::Title:: *)
(*SL(2,\[DoubleStruckCapitalC]) Trace Identities. *)


(* ::Chapter:: *)
(*A companion to Rank 1 Character Varieties of Finitely Presented Groups*)


(* ::Subsubtitle:: *)
(*Jean-Philippe Burelle*)
(*University of Maryland*)
(**)
(*Sean Lawton*)
(*George Mason University*)
(**)
(*August 2017*)
(**)
(*February 2019 update : Optimization of trace reduction algorithm suggested by N. Dunfield*)


(* ::Section:: *)
(*Introduction*)


(* ::Text:: *)
(*The purpose of this notebook is to implement an algorithm which takes as input a finite presentation for a group \[CapitalGamma], and outputs a presentation of the coordinate ring for the corresponding SL(2,C) character variety \[Chi](\[CapitalGamma]).*)
(**)
(*In the "Trace Reduction" section we define a head "Tr" to be used in conjunction with the "Word" head from William Goldman's "Free Group Toolbox". Any Word, when given the "Tr" head will be automatically simplified to a sum of traces of words of length three or less, using SL(2,C) trace identities.*)
(**)
(*The relations for the coordinate ring are coded in the Relations section.*)
(**)
(*The function Presentation uses the previous code to output a presentation of the coordinate ring of a character variety.*)


(* ::Section:: *)
(*Free Group "Word" Code (from William Goldman' s notebook FreeFroupToolboxMathematica NB, available at http://egl.math.umd.edu/software/FreeGroupAutos.m)*)


Unprotect[Word,Dot,Inverse,Equal,Unequal,Power];
Word[a___,m_Integer,n_Integer,b___] := Word[a,b] /; m + n == 0
Dot[Word[],Word[]] := Word[]
Dot[Word[],Word[a__]] := Word[a]
Dot[Word[a__],Word[]] := Word[a]
Dot[Word[a___],Word[b___]] := Word[a,b]
Dot::usage="Dot[Word1,Word2] concatenates the arguments and returns [Word1,Word2].";
Word[a___,0,b___] := Word[a,b]
Inverse[Word[]] := Word[]
Inverse[Word[n_Integer]] := Word[- n]
Inverse[Word[a___,n_Integer]] := Word[- n] . Inverse[Word[a]]
Inverse::usage="Inverse[Word] returns the unique word such that Dot[Word,Inverse[Word]] is the empty word.";
Equal[Word[n___],Word[m___]] := Equal[n,m];
Unequal[Word[n___],Word[m___]]:= Unequal[m,n];
Power[Word[a___],0]:=Word[]
Power[Word[a___],1]:=Word[a]
Power[Word[a___],i_Integer]:=Word[a] . Power[Word[a],i-1]/;i>0
Power[Word[a___],i_Integer]:=Inverse[Power[Word[a],-i]]/;i<0
Protect[Dot,Word,Inverse,Equal,Unequal,Power];


(* ::Section:: *)
(*Trace Reduction*)


Unprotect[Tr];
(* In SL(2,C), the trace of the identity (empty word) is 2 *)
Tr[Word[]]:=2

(* Any word containing a repeated letter X is simplified using the trace identity:
tr(UXVXW)=tr(XV)tr(XWU)-tr(V^-1WU),
where V and U are arbitrary subwords.*)
Tr[Word[w1___,x_Integer,w2___,y_Integer,w3___]]:=Tr[Word[x,w2]]Tr[Word[x,w3,w1]] - Tr[Inverse[Word[w2]] . Word[w3,w1]]/;x==y

(* Any word containing the inverse of a generator X is simplified using the trace identity
tr(UX^-kV)=tr(X^k)tr(VU)-tr(UX^kV).*)
Tr[Word[w1___,x_Integer,w2___]]:=Tr[Word[-x]]Tr[Word[w2,w1]] - Tr[Word[w1,-x,w2]]/;x<0

(* Each word is permuted cyclically so that it becomes minimal for the lexicographic ordering among all its cyclic permutations. *)
Tr[Word[w__]]:=Tr[Sort[Table[RotateLeft[Word[w],k],{k,1,Length[Word[w]]}]][[1]]]/;List[w]!=Sort[Table[RotateLeft[List[w],k],{k,1,Length[List[w]]}]][[1]]

(* After simplyfing to the minimal cyclic ordering we can further simplify to a single lexicographic ordering of the letters by using the trace sum formula for tr(abc)+tr(acb) *)
Tr[Word[x_Integer,y_Integer,z_Integer]]:=-Tr[Word[x,z,y]]+Tr[Word[x]]Tr[Word[y,z]]+Tr[Word[y]]Tr[Word[x,z]]+Tr[Word[z]]Tr[Word[x,y]]-Tr[Word[x]]Tr[Word[y]]Tr[Word[z]]/;x>0&&y>0&&z>0&&x<y&&x<z&&y>z

(* Any word of length 4 or more is reduced using the trace identity for words of length 4 *)
Tr[Word[x_Integer,y_Integer,z_Integer,w__]]:=(1/2)(Tr[Word[x]]Tr[Word[y]]Tr[Word[z]]Tr[Word[w]] + Tr[Word[x]]Tr[Word[y,z,w]] + Tr[Word[y]]Tr[Word[x,z,w]] + Tr[Word[z]]Tr[Word[x,y,w]] + Tr[Word[w]]Tr[Word[x,y,z]] - Tr[Word[x,z]]Tr[Word[y,w]] + Tr[Word[x,w]]Tr[Word[y,z]] + Tr[Word[x,y]]Tr[Word[z,w]] - Tr[Word[x]]Tr[Word[y]]Tr[Word[z,w]] - Tr[Word[x]]Tr[Word[w]]Tr[Word[y,z]] - Tr[Word[y]]Tr[Word[z]]Tr[Word[x,w]] - Tr[Word[z]]Tr[Word[w]]Tr[Word[x,y]])/;(x!=y && y!=z && x>0 && y>0 && z>0)

(*Unprotect[Power]
Power[Tr[Word[x_Integer,y_Integer,z_Integer]],n_]:=Tr[Word[x,y,z]]^(n-2)(4-Tr[Word[x]]^2 - Tr[Word[y]]^2 - Tr[Word[z]]^2 + Tr[Word[x]]Tr[Word[y]]Tr[Word[x,y]] - Tr[Word[x,y]]^2 + Tr[Word[x]]Tr[Word[z]]Tr[Word[x,z]] - Tr[Word[x,z]]^2 + Tr[Word[y]]Tr[Word[z]]Tr[Word[y,z]] - Tr[Word[x,y]]Tr[Word[x,z]]Tr[Word[y,z]] - Tr[Word[y,z]]^2 - Tr[Word[x]]Tr[Word[y]]Tr[Word[z]]Tr[Word[x,y,z]] + Tr[Word[z]]Tr[Word[x,y]]Tr[Word[x,y,z]] + Tr[Word[y]]Tr[Word[x,z]]Tr[Word[x,y,z]] + Tr[Word[x]]Tr[Word[y,z]]Tr[Word[x,y,z]])/;(n>2)
Protect[Power]*)
Protect[Tr];

EvalWord[T_Tr,S_]:=Tr[EvalWord[T[[1]],S]];


(* ::Section:: *)
(*Relations*)


multTraceless[a1_,a2_,a3_]:=5/8Tr[a1]Tr[a2]Tr[a3]-1/2Tr[a3]Tr[a1 . a2]-1/2Tr[a2]Tr[a1 . a3]-1/2Tr[a1]Tr[a2 . a3]+Tr[a1 . a2 . a3]
multTraceless[a1_,a2_]:=Tr[a1 . a2]-1/2Tr[a1]Tr[a2]
s3[a1_,a2_,a3_]:=multTraceless[a1,a2,a3]+multTraceless[a2,a3,a1]+multTraceless[a3,a1,a2]-multTraceless[a1,a3,a2]-multTraceless[a2,a1,a3]-multTraceless[a3,a2,a1]
(*Type 1 relations, for a1<a2<a3*)
rel1[{i1_,i2_,i3_},{j1_,j2_,j3_}]:=s3[Word[i1],Word[i2],Word[i3]]s3[Word[j1],Word[j2],Word[j3]]+18Det[({
 {multTraceless[Word[i1],Word[j1]], multTraceless[Word[i1],Word[j2]], multTraceless[Word[i1],Word[j3]]},
 {multTraceless[Word[i2],Word[j1]], multTraceless[Word[i2],Word[j2]], multTraceless[Word[i2],Word[j3]]},
 {multTraceless[Word[i3],Word[j1]], multTraceless[Word[i3],Word[j2]], multTraceless[Word[i3],Word[j3]]}
})]//Expand
(*Type 2 relations, for p0<p1<p2<p3*)
rel2[i_,{p0_,p1_,p2_,p3_}]:=multTraceless[Word[i],Word[p0]]s3[Word[p1],Word[p2],Word[p3]]-multTraceless[Word[i],Word[p1]]s3[Word[p0],Word[p2],Word[p3]]+multTraceless[Word[i],Word[p2]]s3[Word[p0],Word[p1],Word[p3]]-multTraceless[Word[i],Word[p3]]s3[Word[p0],Word[p1],Word[p2]]//Expand
(*Relations from a presentation of \[CapitalGamma]. Each relation R gives n relations, where n is the number of generators.*)
presrel[R_Word,n_]:=Union[{Tr[R]-Tr[Word[]]},Table[Tr[R . Word[i]]-Tr[Word[i]],{i,1,n}]]//Expand


(* ::Section:: *)
(*Convert traces of words to variables*)


(*ToVariables converts an expression containing Tr[Word[n1,n2,n3]] to variables of the form Subscript[t, n1,n2,n3]*)
ToVariables[expression_]:=expression/.{Tr[Word[n__]]->\!\(\*SubscriptBox[\(t\), \({n}\)]\)}


(* ::Section:: *)
(*Presentations of the Character Variety*)


(* ::Text:: *)
(*The function Presentation takes "n" the number of generators of \[CapitalGamma] and "Relations" a list of Words representing the relations in \[CapitalGamma].*)
(*It outputs a 2-tuple, the first entry is a list of the generators and the second is a list of the relations in the character variety for \[CapitalGamma].*)


Presentation[n_,Relations_]:={(*generators*)Map[Subscript[t, #]&,Subsets[Range[n],{1,3}]],

(*type 1 relations*)
Join[
ToVariables[Map[rel1@@#&,Union[Map[Sort,Tuples[Subsets[Range[n],{3}],{2}]]]]],
(*type 2 relations*)
Flatten[ToVariables[Table[Map[rel2[i,#]&,Subsets[Range[n],{4}]],{i,1,n}]]],
(*relations from relations in \[CapitalGamma]*)
Flatten[ToVariables[Map[presrel[#,n]&,Relations]]]
]
}


(* ::Section:: *)
(*Code to Convert SnapPy syntax to syntax our notebook can read.*)
(**)


(*Takes a word in SnapPy format "AaBbCc" string format and returns the corresponding Word[] object*)
WordFromString[s_] := Module[{chars = ToCharacterCode[s]},
Word@@Map[If[# > 96, # - 96, -(# - 64)] &, chars]]

(*Takes a Word[] and outputs its string representation "AaBbCc"*)
StringFromWord[W_Word]:=FromCharacterCode[Map[If[#>0,#+96,-#+64]&,List@@W]]

(*Takes a list of group presentations outputted from SnapPy and outputs a list of character variety coordinate ring presentations*)
FromSnapPyList[L_]:=Module[{gens,relators,relwords},
gens=Map[(StringLength[#]+1)/2&,StringCases[L,Shortest["Generators:
   "~~x__~~"
Relators:
   "]->x]];
relators=Map[StringSplit,StringCases[L~~"\nG",Shortest["Relators:
   "~~x__~~"
G"]->x]];
relwords=Map[WordFromString,relators,{2}];
MapThread[Print[Presentation[#1,#2]]&,{gens,relwords}];
]


(* ::Section:: *)
(*Example: Free Groups of Rank 1, 2, 3, 4*)


(* ::Input:: *)
(*Presentation[1,{}]*)
(*Presentation[2,{}]*)
(*Presentation[3,{}]*)
(*Presentation[4,{}]*)


(* ::Section:: *)
(**)
(*Example: The first 10 presentations from the Week' s Census of hyperbolic 3-manifold groups (generated by SnapPy):*)


(* ::Input:: *)
(*FromSnapPyList["Generators:*)
(*   a,b*)
(*Relators:*)
(*   aabbaaBaB*)
(*   aabbAbAbb*)
(*Generators:*)
(*   a,b*)
(*Relators:*)
(*   ababAbbAb*)
(*   abAbaabAbaBAB*)
(*Generators:*)
(*   a,b*)
(*Relators:*)
(*   aabbABAbb*)
(*   aBaBabaaab*)
(*Generators:*)
(*   a,b*)
(*Relators:*)
(*   ababAbbAb*)
(*   aabAbaabAbaabAbaaB*)
(*Generators:*)
(*   a,b*)
(*Relators:*)
(*   aBAbaabAB*)
(*   aBAbABabbbbbbb*)
(*Generators:*)
(*   a,b*)
(*Relators:*)
(*   aBAbaabAB*)
(*   abaBAbABabbaBAbAB*)
(*Generators:*)
(*   a,b*)
(*Relators:*)
(*   aBAbaaabAB*)
(*   aBAbABabbbb*)
(*Generators:*)
(*   a,b*)
(*Relators:*)
(*   ababAbbAb*)
(*   abAbaabAbaabAbaBAB*)
(*Generators:*)
(*   a,b*)
(*Relators:*)
(*   ababAbbAb*)
(*   aaBaaBaaBaabAb*)
(*Generators:*)
(*   a,b*)
(*Relators:*)
(*   aBAbaabAB*)
(*   abbaBAbABabbbaBAbAB"]*)



