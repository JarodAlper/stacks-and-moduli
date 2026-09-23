module

public import StacksAndModuli.«Section4.9-Examples».«part4.9.1-examples-of-algebraic-spaces»

/-!
# Examples of Deligne–Mumford stacks and of algebraic stacks

This module records Subsection 4.9.2, "Examples of Deligne–Mumford stacks"
(`subsec:examples-of-DM-stacks`), and Subsection 4.9.3, "Examples of algebraic stacks"
(`subsec:examples-of-algebraic-stacks`), of §4.9 (Further examples) of *Stacks and
Moduli*, section label
`subsec:examples`. It covers `ex:weighted-projective-stack` (Example 4.9.14),
`ex:stacky-curve` (Example 4.9.16), `ex:root-gerbes` (Example 4.9.21), `ex:root-stacks`
(Example 4.9.22), `exer:root-stacks` (Exercise 4.9.23), `ex:classifying-stacks`
(Example 4.9.24), `ex:A1modGm` (Example 4.9.25), `ex:A2modGm` (Example 4.9.28),
`ex:vector-bundle-stacks` (Example 4.9.33, with `eqn:vector-bundle-equivalences`,
Equation 4.9.34) and `exer:vector-bundle-stacks` (Exercise 4.9.35), together with the
unlabeled examples, exercises and remarks between them.

Every example of these two subsections is built from a quotient stack $[U/G]$ or a
classifying stack $\B G = [\Spec \kk / G]$ of a group scheme $G$. None of these can
currently be stated faithfully in Lean: the quotient prestack $[U/G]$ and $\B G$ are
defined via principal $G$-bundles (Appendix B), which have been ledgered since §3.4/§3.5;
Mathlib's `Mathlib.AlgebraicGeometry.Group.*` provides group *objects* in `Over S` and
the Hopf-algebra correspondence, but no group schemes $\bG_m$, $\Gmu_n$, $\GL_n$,
$\PGL_n$, $\bG_a$, no group scheme *actions*, no torsors, and no quotients. Many examples
additionally invoke coarse or good moduli spaces, which are Chapter 6 notions. As no
$[U/G]$-free restatement is faithful, every label of these two subsections is ledgered in
a comment inside its section block below; there are no declarations in this module.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section ExWeightedProjectiveStack

/- LEDGER — the three unlabeled examples opening Subsection 4.9.2
(`subsec:examples-of-DM-stacks`), preceding **Example 4.9.14**
(`ex:weighted-projective-stack`).
- "Classifying stacks": for a finite abstract group scheme $G$ over a field $\kk$, the
  classifying stack $\B G$ (the stack of pairs $(T, P)$ with $P \to T$ a $G$-torsor,
  `def:quotient-prestack-and-stack`, ledgered since §3.4) is a smooth proper
  Deligne–Mumford stack over $\kk$ of dimension 0. Blocked on torsors/principal bundles
  (Appendix B).
- "Simple examples" (char $\kk \neq 2$): (a) $[\bA^1/(\bZ/2)]$ for $(-1) \cdot x = -x$ is
  a smooth DM stack of dimension 1 with a $\bZ/2$-stabilizer at the origin, with coarse
  moduli space $[\bA^1/(\bZ/2)] \to \Spec \kk[x^2] = \bA^1$
  (`thm:quotients-by-finite-groups-cms`, Chapter 6); (b) $[\Spec(\kk[x,y]/(xy))/(\bZ/2)]$
  for $(-1) \cdot (x,y) = (y,x)$ is a singular DM stack with smooth coarse moduli space
  $\bA^1$; (c) $[\bA^2/(\bZ/2)]$ for $(-1) \cdot (x,y) = (-x,-y)$ is a smooth DM stack
  whose coarse moduli space $\Spec \kk[A,B,C]/(B^2 - AC)$ is a singular cone. Blocked on
  quotient stacks and coarse moduli spaces.
- "Quasi-finite but non-finite inertia": for the group scheme
  $G = \bA^1 \amalg (\bA^1 \setminus 0) \to \bA^1$ (fibers $\bZ/2$ away from the origin,
  trivial at the origin), $\B G \to \bA^1$ is a DM stack with quasi-finite but non-finite
  diagonal, hence not separated; similarly for the DM locus of
  $[\Sym^4 \bP^1 / \PGL_2]$ (`ex:four-unordered-points-in-P1`, Example 5.4.17).
  Figure 4.9.13 (`fig:stabilizer-group-jumps-down`) is an illustration only. Blocked on
  classifying stacks. -/

/- LEDGER — **Example 4.9.14** (`ex:weighted-projective-stack`): for positive integers
$(d_0, \ldots, d_n)$, the weighted projective stack is $\cP(d_0, \ldots, d_n) =
[(\bA^{n+1} \setminus 0)/\bG_m]$ for the action $t \cdot (x_0, \ldots, x_n) =
(t^{d_0} x_0, \ldots, t^{d_n} x_n)$; if all $d_i = 1$ it recovers $\bP^n$, and over
$\bZ[1/6]$ one has $\bar{\cM}_{1,1} \cong \cP(4, 6)$
(`exer:stack-of-elliptic-curves-is-algebraic`, Exercise 4.1.21, part (4)). More generally
stacky proj is $\cProj R = [(\Spec R \setminus 0)/\bG_m]$ for a positively graded
$\kk$-algebra $R$. Blocked on $\bG_m$ as a group scheme with its scaling actions and on
quotient stacks (Mathlib has `Proj`, so weighted projective *space* is available, but not
the stack). Stacks Project tag 06FI (algebraicity of quotients by flat groupoids) is the
relevant quotient-stack criterion there. -/

/- LEDGER — the unlabeled exercise following **Example 4.9.14**
(`ex:weighted-projective-stack`). (a) over a
field of characteristic $p$, $\cP(d_0, \ldots, d_n) \times_{\bZ} \kk$ is Deligne–Mumford
iff $p \nmid d_i$ for all $i$; (b) the points of $\cP(3,3,4,6)$ with non-trivial
stabilizer; (c) conditions for generically trivial stabilizer; (d) the bijective coarse
moduli space morphism $\cP(d_0, \ldots, d_n) \to \Proj \kk[x_0, \ldots, x_n]$. Blocked as
the example above, plus coarse moduli spaces (Chapter 6). -/

end ExWeightedProjectiveStack


section ExStackyCurve

/- LEDGER — **Example 4.9.16** (`ex:stacky-curve`) (Stacky curves): a stacky curve is a
one dimensional Deligne–Mumford stack
of finite type over a field; $\cP(m, n)$ is a smooth proper stacky curve when the
characteristic is prime to $m$ and $n$. Blocked on quotient stacks and on the dimension
theory of stacks. -/

/- LEDGER — the unlabeled exercise following **Example 4.9.16** (`ex:stacky-curve`).
(a) a smooth stacky curve has abelian stabilizers; (b) the generalization to nodal stacky
curves. Blocked on stabilizer groups of stacks. -/

/- LEDGER — the unlabeled example "Football curves" (between `ex:stacky-curve`,
Example 4.9.16, and `ex:root-gerbes`, Example 4.9.21). The football curve $\cF(m, n)$ is
the proper stacky curve obtained by gluing $[\bA^1/\Gmu_m]$ and $[\bA^1/\Gmu_n]$ along
$\bA^1 \setminus 0$; its topological space is $|\bP^1|$ and $\cF(m,n) \to \bP^1$ is a
coarse moduli space. Blocked on $\Gmu_n$, quotient stacks, and gluing of stacks. -/

/- LEDGER — the unlabeled exercise following the "Football curves" example.
$\cF(m, n) \cong \cP(m, n)$ if and only if $\gcd(m, n) = 1$. Blocked as above. -/

/- LEDGER (prose) — the unlabeled remark "Uniformization of stacky curves": by
Behrend–Noohi, every smooth separated stacky curve over $\bC$ has a universal cover
isomorphic to $\bH$, $\bC$, or $\cP(m, n)$ with $\gcd(m, n) = 1$. -/

end ExStackyCurve


section ExRootGerbes

/- LEDGER — **Example 4.9.21** (`ex:root-gerbes`) (Root gerbes): for a scheme $X$ with a
line bundle $L$, classified by $[L] \colon X \to \B \bG_m$, and a positive integer $r$,
the $r$-th root gerbe $X(\sqrt[r]{L})$ is the fiber product of $[L]$ with the $r$-th
power map $r \colon \B \bG_m \to \B \bG_m$ (functorially $M \mapsto M^{\otimes r}$);
$X(\sqrt[r]{L}) \to X$ is a banded $\Gmu_r$-gerbe (`exer:root-gerbes-stacks-revisited`,
Exercise 7.4.26) and a coarse moduli space. Blocked on $\B \bG_m$
(`ex:classifying-stacks` below); the alternative functorial description via triples
(`exer:root-stacks` (b)) needs the line-bundle pullback pseudofunctor, the same blocker
as `prop:mss-is-a-stack` (Proposition 3.5.17, §3.5). -/

end ExRootGerbes


section ExRootStacks

/- LEDGER — **Example 4.9.22** (`ex:root-stacks`) (Root stacks): for a scheme $X$, a line
bundle $L$, a section $s \in \Gamma(X, L)$ classified by
$[L, s] \colon X \to [\bA^1/\bG_m]$ (`ex:A1modGm`, Example 4.9.25), and $r \geq 1$, the
$r$-th root stack $X(\sqrt[r]{L,s})$ is the fiber product of $[L, s]$
with the map $r \colon [\bA^1/\bG_m] \to [\bA^1/\bG_m]$ induced by $x \mapsto x^r$
(functorially $(M, t) \mapsto (M^{\otimes r}, t^{\otimes r})$); $\pi \colon
X(\sqrt[r]{L,s}) \to X$ is a coarse moduli space. Caution: $X(\sqrt[r]{L,0})$ is not
isomorphic to the root gerbe $X(\sqrt[r]{L})$, though they have the same reduction. The
coordinatewise power map $x \mapsto x^r$ itself is available:
`AlgebraicGeometry.AffineSpace.pow` (part 4.9.1). Otherwise blocked as
`ex:root-gerbes`. -/

end ExRootStacks


section ExerRootStacks

/- LEDGER — **Exercise 4.9.23** (`exer:root-stacks`): over a scheme $S$ with $r$
invertible in $\Gamma(S, \oh_S)$ (so that $\Gmu_{r,S} \to S$ is étale; the hypothesis is
removed in `exer:root-gerbes-stacks-revisited`, Exercise 7.4.26): (a) $X(\sqrt[r]{L})$ and
$X(\sqrt[r]{L,s})$ are Deligne–Mumford stacks; (b) $X(\sqrt[r]{L})$ is the category of
tuples $(f \colon T \to X, M, \alpha \colon M^{\otimes r} \iso f^* L)$, yielding the
universal $r$-th root $L^{1/r}$; (c) the analogous description of $X(\sqrt[r]{L,s})$ by
tuples $(f, M, \alpha, t)$ with $\alpha(t^{\otimes r}) = f^* s$; (d) for affine
$X = \Spec A$ and trivial $L$, the identifications $X(\sqrt[r]{L}) \cong [X/\Gmu_r]$ and
$X(\sqrt[r]{L,s}) \cong [\Spec(A[x]/(x^r - s))/\Gmu_r]$; (e) the fibers of
$X(\sqrt[r]{L}) \to X$ are $\B \Gmu_{r,\kappa(x)}$; (f) $X(\sqrt[r]{L,s}) \to X$ is an
isomorphism over $\{s \neq 0\}$ and an infinitesimal extension of the root gerbe of
$V(s)$. Blocked on $\Gmu_r$, quotient and classifying stacks, and the line-bundle
pullback pseudofunctor. -/

end ExerRootStacks


section ExClassifyingStacks

/- LEDGER — **Example 4.9.24** (`ex:classifying-stacks`): the classifying stack
$\B \GL_n$ over $\Spec \bZ$ classifies rank-$n$ vector bundles ($\B \bG_m = \B \GL_1$
classifies line bundles). It is a universally closed, smooth algebraic stack over
$\Spec \bZ$ of relative dimension $-n^2$ with affine diagonal, neither separated nor
Deligne–Mumford; $\B \GL_n \to \Spec \bZ$ is a coarse moduli space and a trivially banded
$\GL_n$-gerbe. Blocked on $\GL_n$ as a group scheme and on classifying stacks (principal
bundles, Appendix B); the stack of vector bundles itself was ledgered in §3.4/§3.5
(`prop:mss-is-a-stack`, Proposition 3.5.17, blockers). -/

end ExClassifyingStacks


section ExA1modGm

/- LEDGER — **Example 4.9.25** (`ex:A1modGm`): for the scaling action of $\bG_m$ on
$\bA^1$ over $\Spec \bZ$,
the objects of $[\bA^1/\bG_m]$ over a scheme $T$ are pairs $(L, s)$ of a line bundle with
a section. The stack $[\bA^1/\bG_m]$ is algebraic, universally closed and smooth over
$\Spec \bZ$ of relative dimension 0 with affine diagonal, but neither separated nor
Deligne–Mumford. Over a field it has two points, an open one ($1 \colon \Spec \kk
\hookrightarrow [\bA^1/\bG_m]$) and a closed one ($\B \bG_m \hookrightarrow
[\bA^1/\bG_m]$ at $0$), and $[\bA^1/\bG_m] \to \Spec \kk$ is a good moduli space
(Chapter 6). Blocked on $\bG_m$, its actions, and quotient stacks. -/

/- LEDGER — the unlabeled exercise following **Example 4.9.25** (`ex:A1modGm`).
$[\bP^1/\bG_m] \cong
[(\bA^1 \cup_{\bA^1 \setminus 0} \bA^1)/\bG_m]$. The non-separated affine line appears at
the presheaf level as `AlgebraicGeometry.nonseparatedAffineLinePresheaf` (part 4.9.3);
the statement is blocked on quotient stacks. -/

/- LEDGER — the unlabeled example $[\bP^1/\bG_a]$ (between `ex:A1modGm`, Example 4.9.25,
and `ex:A2modGm`, Example 4.9.28). Over a field $\kk$, the quotient of
$\bP^1$ by the $\bG_a$-action $t \cdot [x : y] = [x + ty : y]$ has two points, the open
point $0 \colon \Spec \kk \hookrightarrow [\bP^1/\bG_a]$ and the closed point
$\B \bG_a \hookrightarrow [\bP^1/\bG_a]$ at $\infty$. Blocked on $\bG_a$-actions and
quotient stacks. -/

end ExA1modGm


section ExA2modGm

/- LEDGER — **Example 4.9.28** (`ex:A2modGm`): over a field $\kk$, for the action
$t \cdot (x, y) = (tx, t^{-1}y)$ of $\bG_m$ on $\bA^2$, the quotient $[\bA^2/\bG_m]$ is a
smooth algebraic
stack of dimension 1 whose $T$-objects are triples $(L, s, t)$ with $s \in \Gamma(T, L)$,
$t \in \Gamma(T, L^{-1})$. The complement of the origin is the non-separated affine line
(cf. `AlgebraicGeometry.nonseparatedAffineLinePresheaf`, part 4.9.3), and $(x, y) \mapsto
xy$ defines a good moduli space $[\bA^2/\bG_m] \to \bA^1$ identifying the three orbits in
$xy = 0$. Blocked on $\bG_m$-actions, quotient stacks, and good moduli spaces. -/

/- LEDGER — the unlabeled exercise "Stacks of representations" (following `ex:A2modGm`,
Example 4.9.28). For a finitely generated
group $\Gamma$ and $n \geq 1$: (a) the stack $\mathrm{Rep}_{\Gamma,n}$ of $n$-dimensional
representations is algebraic; (b) for $\Gamma$ free on $\gamma$ generators,
$\mathrm{Rep}_{\Gamma,n} \cong [\GL_n^{\gamma}/\GL_n]$ (simultaneous conjugation); (c)
for $\Gamma = \pi_1(\Sigma)$ of a genus-$g$ surface, the analogous presentation by the
relation $\prod [\alpha_i, \beta_i] = 1$. Blocked on $\GL_n$ and quotient stacks. -/

/- LEDGER — the unlabeled example "Toric stacks". A stacky fan $(\Sigma, \beta \colon L
\to N)$ defines $G_{\beta} = \ker(T_{\beta} \colon T_L \to T_N)$ and the toric stack
$X(\Sigma, \beta) = [X(\Sigma)/G_{\beta}]$. Blocked on toric varieties (no fans/toric
geometry in Mathlib), diagonalizable group schemes
(`ex:diagonalizable-group-schemes`, Example B.1.7), and quotient stacks. -/

/- LEDGER — the unlabeled example "Picard schemes and stacks" (preceding
`ex:vector-bundle-stacks`, Example 4.9.33). For a proper integral
scheme $X$ over an algebraically closed field, the Picard functor $\uPic(X)$
(sheafification of $T \mapsto \Pic(X_T)$) is representable by a projective group scheme,
and the Picard stack $\ucPic(X)$ (groupoids of line bundles on $X_T$) is a smooth
algebraic stack; $\ucPic(X) \to \uPic(X)$ is a banded $\bG_m$-gerbe (see
`subsec:picard-stack-space`, Subsection 7.4.8). Blocked on the line-bundle pullback
pseudofunctor and on representability of the Picard functor. -/

end ExA2modGm


section ExVectorBundleStacks

/- LEDGER — **Example 4.9.33** (`ex:vector-bundle-stacks`) (Vector bundle stacks): for a
two-term complex $K^{\bullet} \colon K^0
\xrightarrow{d} K^1$ of vector bundles on a scheme $X$, the vector bundle stack is the
quotient stack $\fC(K^{\bullet}) = [\bA(K^{1,\vee})/\bA(K^{0,\vee})]$ over
$(\Sch/X)_{\ét}$, where the additive group scheme $\bA(K^{0,\vee})$ acts by $\sigma(x_0,
x_1) = x_1 + d(x_0)$. Over a point it is $[\H^1(K^{\bullet})/\H^0(K^{\bullet})]$, over an
affine $T \to X$ it is the set-theoretic quotient groupoid $[\H^0(T, g^* K^1)/\H^0(T,
g^* K^0)]$ (using that principal bundles under a vector group over an affine base are
trivial), and $\fC(K^{\bullet}) \to X$ is smooth of relative dimension $\h^1 - \h^0$. The
chain of identifications $\bA(K^{i,\vee})(T \to S) = \H^0(T, g^* K^i)$ is
**Equation 4.9.34** (`eqn:vector-bundle-equivalences`). Blocked on quotient stacks for
group scheme actions and on the total-space construction $\bA(-)$ of a vector bundle with
its additive group structure. -/

end ExVectorBundleStacks


section ExerVectorBundleStacks

/- LEDGER — **Exercise 4.9.35** (`exer:vector-bundle-stacks`): a quasi-isomorphism
$K^{\bullet} \to L^{\bullet}$ of two-term complexes of vector bundles induces an
isomorphism $\fC(K^{\bullet}) \iso \fC(L^{\bullet})$; consequently (per the unlabeled
prose following the exercise) $\fC(K^{\bullet})$ is well defined for
$K^{\bullet} \in D^b(X)$ of amplitude $[0, 1]$ (used for the stack of extensions,
`prop:stack-of-extensions`, Proposition 9.2.13, and the intrinsic normal cone of
Behrend–Fantechi). Blocked as `ex:vector-bundle-stacks` (Example 4.9.33). -/

end ExerVectorBundleStacks
