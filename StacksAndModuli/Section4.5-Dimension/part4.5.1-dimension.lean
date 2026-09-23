module

public import StacksAndModuli.«Section4.3-Properties».«part4.3.4-topological-space»
public import StacksProject.Topology.KrullDimension.«definition-Krull»
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Dimension of algebraic spaces and stacks

This module formalizes **Definition 4.5.1** (`def:dimension-at-a-point`), the unlabeled
well-definedness proposition following it, and **Exercise 4.5.5**
(`exer:dimension-properties`) of §4.5 (Dimension, tangent spaces, and residual gerbes) of
*Stacks and Moduli* (this section carries no
`sec:` label). **Example 4.5.6** (`ex:dimension`, dimensions of quotient and classifying
stacks) is deferred; see the ledger comment in its section and this folder's STATUS.md.

The dimension of a scheme is the Krull dimension of its underlying topological space
(`topologicalKrullDim`), and the dimension at a point is the infimum of the dimensions of
the open neighborhoods of the point (`topologicalKrullDimAtPoint`, Stacks 0055, supplied
by `stacks-project-lean`); both are recalled below. This module extends these notions to
algebraic spaces and stacks.

Main results:

- `AlgebraicGeometry.BasedCategory.etaleDimAt`: the dimension of an algebraic space (or
  Deligne–Mumford stack) at a point of `|𝒳|`, computed on étale presentations;
- `AlgebraicGeometry.BasedCategory.dimAt` and `AlgebraicGeometry.BasedCategory.dim`: the
  dimension of an algebraic stack at a point, `dim_x 𝒳 = dim_u U - dim_{e(u)} R_u`, and
  the dimension of an algebraic stack;
- the well-definedness statements `etaleDimAt_eq_topologicalKrullDimAt` and
  `dimAt_eq_krullDimDiff`, together with the scheme-level dimension formula for smooth
  morphisms (`prop:dimension-for-smooth-morphisms` of Appendix A) and its algebraic-space
  and base-change generalizations (`exer:dimension-properties`), all with deferred proofs.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DefDimensionAtAPoint

open CategoryTheory Functor Limits AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry

/- Background recollection before Definition 4.5.1 (schemes): the *dimension* $\dim X$
of a scheme $X$ is the Krull dimension of its
underlying topological space; this is Mathlib's `topologicalKrullDim`. -/
noncomputable example (X : Scheme.{u}) : WithBot ℕ∞ := topologicalKrullDim X

/- Background recollection before Definition 4.5.1 (schemes): the dimension $\dim_x X$
of a scheme $X$ at a point $x \in X$ is the minimum
of the dimensions of the open subsets containing $x$; this is `topologicalKrullDimAtPoint`
(Stacks 0055, `topology-definition-Krull`), supplied by `stacks-project-lean`. Mathlib
has `topologicalKrullDim` but no pointwise form. -/
noncomputable example (X : Scheme.{u}) (x : X) : WithBot ℕ∞ := topologicalKrullDimAtPoint X x

/-- Background theorem recalled before Definition 4.5.1:
$\dim_x X = \dim \mathcal{O}_{X,x}$ for finite type schemes over a field at closed
points): let $X$ be a scheme locally of finite type over a field $k$ and let $x \in X$ be
a closed point. Then the dimension of $X$ at $x$ equals the Krull dimension of the local
ring $\mathcal{O}_{X,x}$. -/
theorem Scheme.topologicalKrullDimAt_eq_ringKrullDim_stalk {X : Scheme.{u}} {k : Type u}
    [Field k] (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] {x : X}
    (hx : IsClosed ({x} : Set X)) :
    topologicalKrullDimAtPoint X x = ringKrullDim (X.presheaf.stalk x) := by
  sorry

/-- Let $f \colon X \to Y$ be a morphism of schemes and $y \in Y$. The *fiber*
$X_y = X \times_Y \Spec \kappa(y)$ of $f$ over $y$, defined via the canonical morphism
$\Spec \kappa(y) \to Y$. -/
noncomputable def Scheme.Hom.residueFieldFiber {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    Scheme.{u} :=
  pullback f (Y.fromSpecResidueField y)

/-- The projection $X_y \to X$ from the fiber of a morphism of schemes $f \colon X \to Y$
over a point $y \in Y$ to the source. -/
noncomputable def Scheme.Hom.residueFieldFiberFst {X Y : Scheme.{u}} (f : X ⟶ Y)
    (y : Y) : f.residueFieldFiber y ⟶ X :=
  pullback.fst f (Y.fromSpecResidueField y)

section PropDimensionForSmoothMorphisms

/-- **Proposition A.3.10** (`prop:dimension-for-smooth-morphisms`) (the dimension formula
for smooth morphisms, stated here as the scheme-level input to the well-definedness of
the dimension of a stack): let $f \colon X \to Y$ be a smooth morphism of noetherian
schemes and let $x \in X$ with image $y = f(x)$. Then
$\dim_x X = \dim_y Y + \dim_x X_y$, where $X_y = X \times_Y \Spec \kappa(y)$ is the fiber
of $f$ over $y$ and $x$ is identified with the unique point of $X_y$ above it. (From
Appendix A, §A.3 of the book; cf. Stacks 0AFF.) -/
theorem Scheme.topologicalKrullDimAt_eq_add_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNoetherian X] [IsNoetherian Y] [Smooth f] (x : X)
    (z : f.residueFieldFiber (f.base x))
    (hz : (f.residueFieldFiberFst (f.base x)).base z = x) :
    topologicalKrullDimAtPoint X x =
      topologicalKrullDimAtPoint Y (f.base x) +
        topologicalKrullDimAtPoint (f.residueFieldFiber (f.base x)) z := by
  sorry

end PropDimensionForSmoothMorphisms

/-- Helper definition for Definition 4.5.1, part (2): the difference of two
`WithBot ℕ∞`-valued dimensions, valued in
the extended integers
`WithBot (WithTop ℤ)` (`⊥` = dimension of the empty space, `⊤` = infinite dimension).
Conventions: the difference is `⊥` if either argument is `⊥`, and `⊤` if the first
argument is `⊤`; the junk case "finite minus `⊤`" is assigned `⊤` (in the intended uses
the subtrahend is the dimension of a scheme smooth over a field, which noetherian
hypotheses keep finite). -/
def krullDimDiff (d e : WithBot ℕ∞) : WithBot (WithTop ℤ) :=
  WithBot.recBotCoe ⊥
    (fun m ↦ WithBot.recBotCoe ⊥
      (fun n ↦ ((WithTop.recTopCoe ⊤
        (fun a ↦ WithTop.recTopCoe ⊤ (fun b ↦ (((a : ℤ) - (b : ℤ) : ℤ) : WithTop ℤ)) n)
        m : WithTop ℤ) : WithBot (WithTop ℤ))) e) d

/-- The dimension difference with first argument the empty dimension is `⊥`. -/
@[simp]
lemma krullDimDiff_bot_left (e : WithBot ℕ∞) : krullDimDiff ⊥ e = ⊥ :=
  rfl

/-- The dimension difference with second argument the empty dimension is `⊥`. -/
@[simp]
lemma krullDimDiff_bot_right (d : WithBot ℕ∞) : krullDimDiff d ⊥ = ⊥ := by
  induction d using WithBot.recBotCoe <;> simp [krullDimDiff]

/-- The dimension difference with first argument the infinite dimension is `⊤`. -/
@[simp]
lemma krullDimDiff_top_left (n : ℕ∞) :
    krullDimDiff ((⊤ : ℕ∞) : WithBot ℕ∞) (n : WithBot ℕ∞) =
      ((⊤ : WithTop ℤ) : WithBot (WithTop ℤ)) := by
  induction n using WithTop.recTopCoe <;> rfl

/-- On finite dimensions the dimension difference is the difference of integers. -/
@[simp]
lemma krullDimDiff_coe_coe (m n : ℕ) :
    krullDimDiff ((m : ℕ∞) : WithBot ℕ∞) ((n : ℕ∞) : WithBot ℕ∞) =
      ((((m : ℤ) - (n : ℤ) : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) :=
  rfl

namespace BasedCategory

/-- **Definition 4.5.1** (`def:dimension-at-a-point`) (part (1)): let $\cX$ be a prestack
over $\Sch$ and $x \in |\cX|$. The *dimension of $\cX$ at
$x$ computed on étale presentations*: the supremum of the values $\dim_u U$ over all
étale presentations $U \to \cX$ and preimages $u \in U$ of $x$. For a noetherian
algebraic space (or Deligne–Mumford stack) $\cX$, every such presentation computes the
same value (see `etaleDimAt_eq_topologicalKrullDimAt`), which is the book's dimension
$\dim_x \cX \in \mathbb{Z}_{\ge 0} \cup \{\infty\}$; for an algebraic space given as a
presheaf $X$, apply this to the associated prestack
`CategoryTheory.BasedCategory.ofPresheaf X`. -/
noncomputable def etaleDimAt (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u})
    (x : pointSpace 𝒳) : WithBot ℕ∞ :=
  sSup { d | ∃ (U : Scheme.{u}) (p : overBased U ⥤ᵇ 𝒳) (u : U),
    BasedFunctor.RepresentableWith (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u})
      p ∧
    BasedFunctor.mapPoints p (U.toPointSpace u) = x ∧ d = topologicalKrullDimAtPoint U u }

end BasedCategory

namespace BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {U : Scheme.{u}}

/-- Background construction used in Definition 4.5.1, part (2): let
$F \colon \Sch/U \to \cX$ be a morphism of prestacks from a scheme and let
$u \in U$. The fiber $R_u = \Spec \kappa(u) \times_{\cX} U$ of the source map of the
induced groupoid $R = U \times_{\cX} U \rightrightarrows U$ over $u$, realized directly
as the prestack fiber product of $\Spec \kappa(u) \to U \to \cX$ and $U \to \cX$. For a
smooth presentation $F$ of an algebraic stack it is (represented by) an algebraic space
smooth over $\kappa(u)$. -/
noncomputable abbrev residueFieldFiberProduct (F : overBased U ⥤ᵇ 𝒳) (u : U) :
    BasedCategory Scheme.{u} :=
  fiberProduct ((overBased.map (U.fromSpecResidueField u)).comp F) F

/-- The canonical section of the fiber $R_u = \Spec \kappa(u) \times_{\cX} U$: the
morphism $\Sch/\Spec \kappa(u) \to R_u$ induced by the identity of $\Spec \kappa(u)$,
the canonical morphism $\Spec \kappa(u) \to U$, and the identity 2-isomorphism. It
corresponds to the identity $e(u)$ of the groupoid $R \rightrightarrows U$ at $u$. -/
noncomputable def residueFieldFiberProductLift (F : overBased U ⥤ᵇ 𝒳) (u : U) :
    overBased (Spec (U.residueField u)) ⥤ᵇ residueFieldFiberProduct F u :=
  fiberProductLift (BasedFunctor.id _) (overBased.map (U.fromSpecResidueField u))
    (eqToIso (show (BasedFunctor.id _).comp
        ((overBased.map (U.fromSpecResidueField u)).comp F) =
      (overBased.map (U.fromSpecResidueField u)).comp F from rfl))

/-- Background construction used in Definition 4.5.1, part (2): the point
$e(u) \in |R_u|$ of the fiber $R_u = \Spec \kappa(u) \times_{\cX} U$
determined by the canonical section: the class of the field-valued point
$\Spec \kappa(u) \to R_u$ given by `residueFieldFiberProductLift`. -/
noncomputable def residueFieldFiberProductPoint (F : overBased U ⥤ᵇ 𝒳) (u : U) :
    pointSpace (residueFieldFiberProduct F u) :=
  pointSpace.mk
    { carrier := U.residueField u
      hom := residueFieldFiberProductLift F u }

end BasedFunctor

namespace BasedCategory

/-- **Definition 4.5.1** (`def:dimension-at-a-point`) (part (2)): let $\cX$ be a prestack
over $\Sch$ and $x \in |\cX|$. The *dimension of $\cX$ at
$x$*: the supremum of the values $\dim_u U - \dim_{e(u)} R_u$ over all smooth
presentations $U \to \cX$ and preimages $u \in U$ of $x$, where
$R_u = \Spec \kappa(u) \times_{\cX} U$ and $e(u) \in |R_u|$ is the identity point
(`AlgebraicGeometry.BasedFunctor.residueFieldFiberProduct` and
`residueFieldFiberProductPoint`), and the difference is taken in
$\mathbb{Z} \cup \{\pm\infty\}$ via `AlgebraicGeometry.krullDimDiff`. For a noetherian
algebraic stack every such presentation computes the same value (see
`dimAt_eq_krullDimDiff`), which is the book's
$\dim_x \cX \in \mathbb{Z} \cup \{\infty\}$. -/
noncomputable def dimAt (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) (x : pointSpace 𝒳) :
    WithBot (WithTop ℤ) :=
  sSup { d | ∃ (U : Scheme.{u}) (F : overBased U ⥤ᵇ 𝒳) (u : U),
    BasedFunctor.RepresentableWith (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u})
      F ∧
    BasedFunctor.mapPoints F (U.toPointSpace u) = x ∧
    d = krullDimDiff (topologicalKrullDimAtPoint U u)
      (etaleDimAt _ (BasedFunctor.residueFieldFiberProductPoint F u)) }

/-- **Definition 4.5.1** (`def:dimension-at-a-point`) (part (3)): let $\cX$ be a prestack
over $\Sch$. The *dimension of $\cX$* is the supremum of the
dimensions of $\cX$ at the points of $|\cX|$. For a noetherian algebraic space or stack
this is the book's $\dim \cX \in \mathbb{Z} \cup \{\infty\}$. -/
noncomputable def dim (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) : WithBot (WithTop ℤ) :=
  ⨆ x : pointSpace 𝒳, dimAt 𝒳 x

/-- The unnumbered well-definedness proposition following Definition 4.5.1 (space case):
well-definedness of the dimension of an algebraic
space (or Deligne–Mumford stack) at
a point: if $\cX$ is a locally noetherian Deligne–Mumford stack — in particular a
noetherian algebraic space — then every étale presentation $U \to \cX$ and preimage
$u \in U$ of a point $x \in |\cX|$ computes the dimension of $\cX$ at $x$: étale
morphisms have relative dimension $0$. -/
theorem etaleDimAt_eq_topologicalKrullDimAt {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}
    [IsDeligneMumfordStack 𝒳] (hln : IsLocallyNoetherian 𝒳) {U : Scheme.{u}}
    {p : overBased U ⥤ᵇ 𝒳}
    (hp : BasedFunctor.RepresentableWith
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) p)
    {u : U} {x : pointSpace 𝒳} (hu : BasedFunctor.mapPoints p (U.toPointSpace u) = x) :
    etaleDimAt 𝒳 x = topologicalKrullDimAtPoint U u := by
  sorry

/-- The unnumbered well-definedness proposition following Definition 4.5.1 (stack case):
if $\cX$ is a
locally noetherian algebraic stack, then every smooth presentation $U \to \cX$ and
preimage $u \in U$ of a point $x \in |\cX|$ computes the dimension of $\cX$ at $x$ as
$\dim_u U - \dim_{e(u)} R_u$. (The proof dominates two presentations by
$U \times_{\cX} U'$ and applies the dimension formula for smooth morphisms,
Proposition A.3.10, together with its
algebraic-space generalization and the field-extension invariance of
Exercise 4.5.5.) -/
theorem dimAt_eq_krullDimDiff {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}
    [IsAlgebraicStack 𝒳] (hln : IsLocallyNoetherian 𝒳) {U : Scheme.{u}}
    {F : overBased U ⥤ᵇ 𝒳}
    (hF : BasedFunctor.RepresentableWith
      (@Surjective ⊓ @Smooth : MorphismProperty Scheme.{u}) F)
    {u : U} {x : pointSpace 𝒳} (hu : BasedFunctor.mapPoints F (U.toPointSpace u) = x) :
    dimAt 𝒳 x = krullDimDiff (topologicalKrullDimAtPoint U u)
      (etaleDimAt _ (BasedFunctor.residueFieldFiberProductPoint F u)) := by
  sorry

end BasedCategory

end AlgebraicGeometry

end DefDimensionAtAPoint

section ExerDimensionProperties

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedCategory

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- Let $F \colon \cX \to \cY$ be a morphism of prestacks over $\Sch$ and let
$\bar{x} \colon \Spec K \to \cX$ be a field-valued point. The canonical field-valued
point of the fiber $\cX \times_{\cY} \Spec K$ of $F$ over the image point
$F \circ \bar{x}$, induced by $\bar{x}$, the identity of $\Spec K$, and the identity
2-isomorphism. -/
noncomputable def FieldPoint.toFiberProduct (x : FieldPoint 𝒳) (F : 𝒳 ⥤ᵇ 𝒴) :
    FieldPoint (fiberProduct F (x.map F).hom) where
  carrier := x.carrier
  hom := fiberProductLift x.hom (BasedFunctor.id _)
    (eqToIso (show x.hom.comp F = (BasedFunctor.id _).comp ((x.map F).hom) from rfl))

end AlgebraicGeometry.BasedCategory

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- **Exercise 4.5.5** (`exer:dimension-properties`) (part (a): the dimension formula for
smooth morphisms of algebraic spaces): let $F \colon \cX \to
\cY$ be a smooth morphism of locally noetherian algebraic spaces (realized as
Deligne–Mumford prestacks represented by algebraic-space presheaves) and let $\bar{x}
\colon \Spec K \to \cX$ be a field-valued point with class $x \in |\cX|$ and image $y \in
|\cY|$. Then $\dim_x \cX = \dim_y \cY + \dim_{\bar x} \cX_y$, where $\cX_y = \cX
\times_{\cY} \Spec K$ is the fiber of $F$ over the representative $F \circ \bar{x}$ of
$y$, at the canonical lift of $\bar{x}$. This generalizes Proposition A.3.10 to
algebraic spaces. -/
theorem etaleDimAt_eq_add_of_smooth [IsDeligneMumfordStack 𝒳] [IsDeligneMumfordStack 𝒴]
    (h𝒳 : ∃ X : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace X ∧ 𝒳.IsRepresentedByPresheaf X)
    (h𝒴 : ∃ Y : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace Y ∧ 𝒴.IsRepresentedByPresheaf Y)
    (hln𝒳 : BasedCategory.IsLocallyNoetherian 𝒳)
    (hln𝒴 : BasedCategory.IsLocallyNoetherian 𝒴) {F : 𝒳 ⥤ᵇ 𝒴}
    (hF : Smooth F) (x : FieldPoint 𝒳) :
    etaleDimAt 𝒳 (pointSpace.mk x) =
      etaleDimAt 𝒴 (mapPoints F (pointSpace.mk x)) +
        etaleDimAt (fiberProduct F (x.map F).hom)
          (pointSpace.mk (FieldPoint.toFiberProduct x F)) := by
  sorry

end AlgebraicGeometry.BasedFunctor

namespace AlgebraicGeometry.BasedCategory

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}

/-- **Exercise 4.5.5** (`exer:dimension-properties`) (part (b): invariance of dimension
under field extensions): let $\cX$ be a locally noetherian
algebraic stack over a field $k$ (via a structural morphism $\cX \to \Sch/\Spec k$), let
$k \to k'$ be a field extension, and let $x' \in |\cX_{k'}|$ be a point of the base
change $\cX_{k'} = \cX \times_{\Spec k} \Spec k'$ with image $x \in |\cX|$. Then
$\dim_{x'} \cX_{k'} = \dim_x \cX$. -/
theorem dimAt_fiberProduct_eq_dimAt [IsAlgebraicStack 𝒳]
    (hln : IsLocallyNoetherian 𝒳) {k k' : Type u} [Field k] [Field k'] (i : k →+* k')
    (P : 𝒳 ⥤ᵇ overBased (Spec (CommRingCat.of k)))
    {x' : pointSpace (fiberProduct P
      (overBased.map (Spec.map (CommRingCat.ofHom i))))}
    {x : pointSpace 𝒳}
    (hx : BasedFunctor.mapPoints
      (fiberProductFst P (overBased.map (Spec.map (CommRingCat.ofHom i)))) x' = x) :
    dimAt (fiberProduct P (overBased.map (Spec.map (CommRingCat.ofHom i)))) x' =
      dimAt 𝒳 x := by
  sorry

end AlgebraicGeometry.BasedCategory

end ExerDimensionProperties

section ExDimension

/- LEDGER (**Example 4.5.6**, `ex:dimension`): for a smooth affine algebraic group `G`
over a field `k`
acting on a pure dimensional scheme `U` of finite type over `k`, the quotient stack
satisfies `dim [U/G] = dim U - dim G`; in particular `dim BG = -dim G` (which can be
negative) and `dim [𝔸¹/𝔾ₘ] = 0`. Blocked on the quotient stacks `[U/G]` and classifying
stacks `BG` (§3.4/§3.5 ledgers) and on `thm:quotient-stack-is-algebraic` (§4.1 ledger;
cf. Stacks 06FI). -/

end ExDimension
