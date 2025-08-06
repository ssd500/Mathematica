MatrixForm[a={{1},{0}}];
MatrixForm[b={{0},{1}}];
MatrixForm[S={{1,0,0,0},{0,0,1,0},{0,1,0,0},{0,0,0,1}}];
(* Q = Normal[SparseArray[Band[{1,1},{d,d}]->1,{2^n,2^n}]]; *)

kpl[l_]:=(KroneckerProduct @@ l)
ent[l_]:=(supp[den[Total[kpl /@ l]]])
mix[l_]:=(supp[Total[den/@kpl /@ l]])
supp[m_]:=(l=ConjugateTranspose[Orthogonalize[ConjugateTranspose[m]]];l.ConjugateTranspose[l])
den[m_]:=m.ConjugateTranspose[m]
trace[m_,l_]:=(ResourceFunction["MatrixPartialTrace"][m, l, 2])
inter[l_]:=(j=Length[l[[1]]];r=supp[Total[(IdentityMatrix[j]-#)&/@l]];IdentityMatrix[j]-r)
apply[u_,m_]:=(u.m.ConjugateTranspose[u])
display[l_]:=(Print[MatrixForm[#]&/@Replace[l, _?(Not@*AssociationQ) :> {l}]])
rank[m_]:=(Print[MatrixRank[m]])
hermitian[m_]:=(Print[HermitianMatrixQ[m]])
unitary[m_]:=(Print[UnitaryMatrixQ[m]])
psd[m_]:=(Print[PositiveSemidefiniteMatrixQ[m]])
expand[a_]:=(x=Keys[a];y=Values[a];z=Join[x,Complement[B,x]];d=Length[z]-Length[x];y=KroneckerProduct[y,IdentityMatrix[2^d]];z=z//.{g1___,g2_,g3_,g4___}/;g2>g3:>(p=Length[{g1}];q=Length[{g4}];w=KroneckerProduct[IdentityMatrix[2^p],S,IdentityMatrix[2^q]];y=apply[w,y];{g1,g3,g2,g4});<|x->y|>)
closure[Q_]:=(B=Range[n];A=Subsets[B,{k}];P=Simplify[supp[trace[Q,Complement[B,#]]]]&/@A;AP=AssociationThread[A,P];(* display[AP]; *)AP=AssociationMap[expand,AP];inter[Values[AP]])

n=3;
k=2;
H={{1/Sqrt[2], 1/Sqrt[2]}, {1/Sqrt[2], -1/Sqrt[2]}};
h=KroneckerProduct[H, H, H];
(* display[h] *)
(* Print["f"];
f=2*apply[h, ent[{{a, a, a}}]] - IdentityMatrix[2^n];
display[f] *)
c1=ent[{{a, a, a}}];
c=supp[c1];
Print["c"]
display[c]
rank[c]
Ac=closure[c];
Print["Ac"]
display[Ac]
rank[Ac]
(* Afc=closure[apply[f, c]];
Print["Afc"]
display[Afc]
rank[Afc]
AfAc=closure[apply[f, closure[c]]];
Print["AfAc"]
display[AfAc]
rank[AfAc]
Print["Local Completeness for f"]
Print[AfAc == Afc] *)
(* f = {{-3/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4}, {1/4, -3/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4}, {1/4, 1/4, -3/4, 1/4, 1/4, 1/4, 1/4, 1/4}, {1/4, 1/4, 1/4, -3/4, 1/4, 1/4, 1/4, 1/4}, {1/4, 1/4, 1/4, 1/4, -3/4, 1/4, 1/4, 1/4}, {1/4, 1/4, 1/4, 1/4, 1/4, -3/4, 1/4, 1/4}, {1/4, 1/4, 1/4, 1/4, 1/4, 1/4, -3/4, 1/4}, {1/4, 1/4, 1/4, 1/4, 1/4, 1/4, 1/4, -3/4}}; *)
(* display[f.g] *)
(* unitary[f] *)
f1=h;
g1=ConjugateTranspose[f1];
Print["f1"]
display[f1]
unitary[f1]
f2=IdentityMatrix[2^n];
f2[[1, 1]]=-1;
f2[[7, 7]]=-1;
g2=ConjugateTranspose[f2];
Print["f2"]
display[f2]
unitary[f2]
f3=2*apply[h, ent[{{a, a, a}}]] - IdentityMatrix[2^n];
g3=ConjugateTranspose[f3];
Print["f3"]
display[f3]
unitary[f3]
c2 = apply[f1, c];
c3 = apply[f2, c2];

Af1c=closure[apply[f1, c]];
Print["Af1c"]
display[Af1c]
rank[Af1c]
Af1Ac=closure[apply[f1, closure[c]]];
Print["Af1Ac"]
display[Af1Ac]
rank[Af1Ac]
Print["Local Completeness for f1"]
Print[Af1Ac == Af1c]

Af2c2=closure[Simplify[apply[f2, c2]]];
Print["Af2c2"]
display[Af2c2]
rank[Af2c2]
Af2Ac2=closure[Simplify[apply[f2, closure[c2]]]];
Print["Af2Ac2"]
display[Af2Ac2]
rank[Af2Ac2]
Print["Local Completeness for f2"]
Print[Af2Ac2 == Af2c2]
(* Ac2=closure[c2]
Print["Ac2"]
rank[Ac2]
display[Ac2]
g2Af2c2=Simplify[apply[g2, Af2c2]];
Print["Fat L2"]
display[supp[g2Af2c2]]
rank[g2Af2c2]
u=inter[{Ac2,g2Af2c2}];
Print["Actual u for f2"]
display[u]
rank[u] *)

Af3c3=closure[Simplify[apply[f3, c3]]];
Print["Af3c3"]
display[Af3c3]
rank[Af3c3]
Af3Ac3=closure[Simplify[apply[f3, closure[c3]]]];
Print["Af3Ac3"]
display[Af3Ac3]
rank[Af3Ac3]
Print["Local Completeness for f3"]
Print[Af3Ac3 == Af3c3]
Ac3=closure[c3]
Print["Ac3"]
rank[Ac3]
display[Ac3]
g3Af3c3=Simplify[apply[g3, Af3c3]];
Print["Fat L3"]
display[g3Af3c3]
rank[g3Af3c3]
u=inter[{Ac3,g3Af3c3}];
Print["Actual u for f3"]
display[u]
rank[u]

v4=Af3c3;
a3=closure[Simplify[apply[f2,Af1Ac]]];
Print["a3"]
display[a3]
rank[a3]
w3=g3Af3c3;
v3=inter[{a3,w3}];
Print["v3"]
display[v3]
rank[v3]
a2=Af1Ac;
w2=Simplify[apply[g2, v3]];
Print["w2"]
display[w2]
rank[w2]
v2=inter[{a2,w2}];
Print["v2"]
display[v2]
rank[v2]
a1=closure[c];
w1=Simplify[apply[g1, v2]];
v1=inter[{a1,w1}];
Print["v1"]
display[v1]
rank[v1]
Print["bca"]
a4=closure[Simplify[apply[f3,a3]]];
display[a4]
rank[a4]
