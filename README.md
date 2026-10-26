This is the magma code to the algebraic Brauer groups of affine surface U:x^4+y^4+n=w^2 (a "Fermat near miss")
and of its projectivization X:x^4+y^4+nz^4=w^2, in the case when n is a square.
We use the conic bundle structure and the fact that the splitting field of X is a Galois extension
with Galois group (Z/2Z)^3, acting on the lines of X.
We reduce to the case when the Brauer group of X is (Z/2Z)^2, which is the case when n=m^2 with m>1 odd squarefree
(one can check this in the paper "On the arithmetic of del Pezzo surfaces of degree 2" by Andrew Kresch and Yuri Tschinkel)

This code is based on the code in Algebraic_Brauer_Group.m used in the paper by Dan Loughran and Vladimir Mitankin,
" Integral Hasse principle and strong approximation for Markoff surfaces", International Mathematics Research Notices, 2021.
