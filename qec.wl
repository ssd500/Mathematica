n = 3;
MatrixForm[a = {{1}, {0}}];
MatrixForm[b = {{0}, {1}}];
MatrixForm[ID = IdentityMatrix[2^n]];
MatrixForm[ZE = ConstantArray[0, {2^n, 2^n}]];

kpl[l_] := (KroneckerProduct @@ l)
den[m_] := (m.ConjugateTranspose[m])
oc[m_] := (ID - m)
null[m_] := (bv=NullSpace[m]; If[Length[bv] == 0, ZE, ConjugateTranspose[bv].bv])
supp[m_] := (oc[null[m]])
join[l_] := (supp[Total[l]])
meet[l_] := (oc[join[oc /@ l]])
ent[l_] := (supp[den[Total[kpl /@ l]]])
mix[l_] := (supp[Total[den /@ kpl /@ l]])

apply[u_,m_] := (u.m.ConjugateTranspose[u])
rank[m_] := (Print[MatrixRank[m]])
psd[m_] := (Print[PositiveSemidefiniteMatrixQ[m]])

x = mix[{{a, a, a}}];
y = mix[{{b, b, b}}];
MatrixForm[x]
MatrixForm[y]
MatrixForm[join[{x, y}]]
MatrixForm[meet[{x, y}]]
