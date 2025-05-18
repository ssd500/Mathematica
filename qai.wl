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
psd[m_]:=(Print[PositiveSemidefiniteMatrixQ[m]])
expand[a_]:=(x=Keys[a];y=Values[a];z=Join[x,Complement[B,x]];d=Length[z]-Length[x];y=KroneckerProduct[y,IdentityMatrix[2^d]];z=z//.{g1___,g2_,g3_,g4___}/;g2>g3:>(p=Length[{g1}];q=Length[{g4}];w=KroneckerProduct[IdentityMatrix[2^p],S,IdentityMatrix[2^q]];y=apply[w,y];{g1,g3,g2,g4});<|x->y|>)
closure[Q_]:=(B=Range[n];A=Subsets[B,{k}];P=supp[trace[Q,Complement[B,#]]]&/@A;AP=AssociationThread[A,P];display[AP];AP=AssociationMap[expand,AP];inter[Values[AP]])

n=5;
k=2;
c1=mix[{{a, b, b, a, b}, {b, b, a, b, a}, {a, a, b, a, a}, {a, b, a, a, a}, {b, a, a, a, a}}];
c2=ent[{{b, b, b, b, a}, {b, b, b, a, b}, {b, b, a, b, b}, {b, a, b, b, b}, {a, b, b, b, b}}];
c=supp[c1];
Print["c"]
rank[c]
f=IdentityMatrix[2^n];
f[[{1,2}]]=f[[{2,1}]];
g=ConjugateTranspose[f];
Print["f"]
Print[f.g == g.f]
fc=apply[f, c];
Print["fc"]
Afc=closure[fc];
Print["Afc"]
rank[Afc]
Ac=closure[c];
Print["Ac"]
rank[Ac]
Print["fAc"]
fAc=apply[f, Ac];
AfAc=closure[fAc];
Print["AfAc"]
rank[AfAc]
diff=AfAc-Afc;
Print["Local Completeness"]
Print[AfAc == Afc]
Print["Degree of Incompleteness"]
psd[diff]
rank[diff]
gAfc=apply[g, Afc];
u=inter[{Ac,gAfc}];
Print["Actual u"]
psd[u]
rank[u]
d0=Ac-u;
Print["Candidate below Ac"]
psd[d0]
rank[d0]
fu=apply[f, u];
d00=Afc-fu;
Print["fCandidate below Afc"]
psd[d00]
rank[d00]