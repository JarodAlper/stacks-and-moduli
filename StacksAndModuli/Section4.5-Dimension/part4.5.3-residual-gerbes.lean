module

public import StacksAndModuli.«Section4.3-Properties».«part4.3.4-topological-space»
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.LocallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksAndModuli.API.FiniteTypeResidueField

/-!
# Residual gerbes

This module formalizes **Definition 4.5.12** (`def:residual-gerbe`),
**Definition 4.5.13** (`def:finite-type-point`) (with the unlabeled remark following it),
**Exercise 4.5.15** (`exer:finite-type-points`), **Proposition 4.5.16**
(`prop:residual-gerbe-algebraic`), and **Exercise 4.5.17** (`exer:dim-0-algebraic-space`)
of §4.5 (Dimension, tangent spaces, and residual gerbes) of
*Stacks and Moduli* (this section carries no
`sec:` label). **Exercise 4.5.18** (`exer:non-noetherian-residual-gerbes-DM`), the
unlabeled orbit corollary (anchored at **Equation 4.5.20**, `eqn:residual-gerbe-orbit`),
**Remark 4.5.21** (`rmk:orbit-cartesian-diagram`), and **Exercise 4.5.22**
(`exer:dimension-of-residual-gerbe`) are deferred; see
the ledger comments in their sections and this folder's STATUS.md.

Attached to every point of a scheme is its residue field with a monomorphism
`Spec κ(x) → X`. For algebraic stacks, non-trivial stabilizers prevent field-valued
points from being monomorphisms, and the *residual gerbe* is the replacement: a reduced,
locally noetherian algebraic stack `𝒢ₓ` with a monomorphism `𝒢ₓ ↪ 𝒳` whose space of
points is a single point mapping to `x`. Monomorphisms of stacks are spelled as fully
faithful morphisms (cf. Stacks 04ZZ).

Main results:
- `AlgebraicGeometry.BasedCategory.HasResidualGerbeAt`: the existence of a residual
  gerbe at a point;
- `AlgebraicGeometry.BasedCategory.IsFiniteTypePoint`: finite type points of `|𝒳|`;
- the statements (with deferred proofs) of the characterization of finite type points
  (`exer:finite-type-points`), the existence and uniqueness of residual gerbes at finite
  type points with their properties (`prop:residual-gerbe-algebraic`), and the
  identification of reduced one-point noetherian algebraic spaces with spectra of fields
  (`exer:dim-0-algebraic-space`).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section DefResidualGerbe

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

/-- Supporting predicate for Definition 4.5.12: let $\cX$ be a prestack over $\Sch$ and
$x \in |\cX|$. A morphism of
prestacks
$F \colon \cG \to \cX$ is a *residual gerbe at $x$* if $\cG$ is a reduced, locally
noetherian algebraic stack, $F$ is a monomorphism — spelled as a fully faithful functor,
cf. Stacks 04ZZ — and $|\cG|$ is a single point mapping to $x$. -/
structure IsResidualGerbeAt {𝒢 : BasedCategory.{v₃, u₃} Scheme.{u}}
    {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} (F : 𝒢 ⥤ᵇ 𝒳) (x : pointSpace 𝒳) :
    Prop where
  /-- The source is an algebraic stack. -/
  isAlgebraicStack : IsAlgebraicStack 𝒢
  /-- The source is reduced. -/
  isReduced : BasedCategory.IsReduced 𝒢
  /-- The source is locally noetherian. -/
  isLocallyNoetherian : BasedCategory.IsLocallyNoetherian 𝒢
  /-- The inclusion is full. -/
  full : F.toFunctor.Full
  /-- The inclusion is faithful. -/
  faithful : F.toFunctor.Faithful
  /-- The space of points of the source is a single point. -/
  subsingleton_pointSpace : Subsingleton (pointSpace 𝒢)
  /-- The image of the points of the source is exactly the point `x`. -/
  range_mapPoints : Set.range (mapPoints F) = {x}

end AlgebraicGeometry.BasedFunctor

namespace AlgebraicGeometry.BasedCategory

/-- **Definition 4.5.12** (`def:residual-gerbe`): let $\cX$ be a prestack over $\Sch$
and $x \in |\cX|$. The *residual gerbe at $x$
exists* if there are a reduced, locally noetherian algebraic stack $\cG_x$ and a
monomorphism $\cG_x \hookrightarrow \cX$ such that $|\cG_x|$ is a point mapping to $x$.
(The algebraic stack $\cG_x$ is called the residual gerbe at $x$; it is unique by
Proposition 4.5.16. The residual gerbes quantified
here live in the same universes as $\cX$.) -/
def HasResidualGerbeAt (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) (x : pointSpace 𝒳) :
    Prop :=
  ∃ (𝒢 : BasedCategory.{v₂, u₂} Scheme.{u}) (F : 𝒢 ⥤ᵇ 𝒳),
    BasedFunctor.IsResidualGerbeAt F x

/- The book's discussion after `def:residual-gerbe`: gerbes are defined in
**Definition 7.4.6** (`def:gerbes`), where it is shown that a residual gerbe `𝒢ₓ` is a
gerbe over a field
`κ(x)`, the *residue field* of `x` (**Proposition 7.4.39**,
`prop:residual-gerbe-algebraic2`); the existence of
residual gerbes at arbitrary points of quasi-separated stacks is deferred to
`subsec:residual-gerbes-revisited`. Here only the existence at finite type points is
treated (**Proposition 4.5.16**, `prop:residual-gerbe-algebraic`, below). -/

end AlgebraicGeometry.BasedCategory

end DefResidualGerbe

section DefFiniteTypePoint

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.BasedCategory

/-- **Definition 4.5.13** (`def:finite-type-point`): let $\cX$ be a prestack over
$\Sch$. A point $x \in |\cX|$ is *of finite type* if
there exists a representative $\Spec k \to \cX$ of $x$ that is locally of finite type.
(If $\cX$ has quasi-compact diagonal — e.g. $\cX$ is quasi-separated — every field-valued
point is automatically quasi-compact, and locally of finite type is then equivalent to
finite type; the diagonal is a §4.2 notion and this refinement is not recorded here.) -/
def IsFiniteTypePoint (𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}) (x : pointSpace 𝒳) :
    Prop :=
  ∃ p : FieldPoint 𝒳, pointSpace.mk p = x ∧ BasedFunctor.LocallyOfFiniteType p.hom

end AlgebraicGeometry.BasedCategory

namespace AlgebraicGeometry

/-- STEP 0, generalized to an arbitrary open immersion. -/
theorem Scheme.locallyOfFiniteType_fromSpecResidueField_transport {Y X : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] (y : Y) :
    LocallyOfFiniteType (X.fromSpecResidueField (f y)) ↔
      LocallyOfFiniteType (Y.fromSpecResidueField y) := by
  have key : Spec.map (f.residueFieldMap y) ≫ X.fromSpecResidueField (f y) =
      Y.fromSpecResidueField y ≫ f :=
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (f := f) y
  have hiso : IsIso (Spec.map (f.residueFieldMap y)) := inferInstance
  constructor
  · intro h
    have h2 : LocallyOfFiniteType (Y.fromSpecResidueField y ≫ f) := by
      rw [← key]; infer_instance
    exact locallyOfFiniteType_of_comp _ f
  · intro h
    have h2 : LocallyOfFiniteType (Spec.map (f.residueFieldMap y) ≫
        X.fromSpecResidueField (f y)) := by rw [key]; infer_instance
    exact (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType
      (Spec.map (f.residueFieldMap y)) (X.fromSpecResidueField (f y))).mp h2

/-- The (⇐) direction. -/
theorem Scheme.isLocallyClosed_singleton_backward {X : Scheme.{u}} (x : X) (h : IsLocallyClosed ({x} : Set X)) :
    LocallyOfFiniteType (X.fromSpecResidueField x) := by
  obtain ⟨V, Z, hV, hZ, hVZ⟩ := h
  have hxV : x ∈ V := by
    have : x ∈ ({x} : Set X) := rfl
    rw [hVZ] at this; exact this.1
  have hxZ : x ∈ Z := by
    have : x ∈ ({x} : Set X) := rfl
    rw [hVZ] at this; exact this.2
  let U : X.Opens := ⟨V, hV⟩
  have hcl : IsClosed ({(⟨x, hxV⟩ : U.toScheme)} : Set U.toScheme) := by
    have : ({(⟨x, hxV⟩ : U.toScheme)} : Set U.toScheme) = (Subtype.val) ⁻¹' Z := by
      ext ⟨y, hy⟩
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · intro he
        have hyx : y = x := congrArg Subtype.val he
        subst hyx; exact hxZ
      · intro hyZ
        have hy' : y ∈ ({x} : Set X) := by rw [hVZ]; exact ⟨hy, hyZ⟩
        exact Subtype.ext hy'
    rw [this]
    exact hZ.preimage continuous_subtype_val
  have : IsClosedImmersion (U.toScheme.fromSpecResidueField ⟨x, hxV⟩) :=
    isClosed_singleton_iff_isClosedImmersion.mp hcl
  have := (Scheme.locallyOfFiniteType_fromSpecResidueField_transport U.ι
    (⟨x, hxV⟩ : U.toScheme)).mpr inferInstance
  exact this

/-- Step (b): reduce to an algebra statement over an affine. -/
theorem Scheme.finiteType_of_locallyOfFiniteType (R : CommRingCat.{u}) (p : Spec R)
    (h : LocallyOfFiniteType ((Spec R).fromSpecResidueField p)) :
    Algebra.FiniteType R p.asIdeal.ResidueField := by
  have e := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField R p
  rw [← e] at h
  have h2 : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (algebraMap R p.asIdeal.ResidueField))) :=
    (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType _ _).mp h
  have h3 := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h2
  exact RingHom.finiteType_algebraMap.mp h3

theorem Scheme.isLocallyClosed_image_of_isOpenImmersion {Y X : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] (y : Y)
    (h : IsLocallyClosed ({y} : Set Y)) : IsLocallyClosed ({g y} : Set X) := by
  have := h.image (f := g.base) g.isOpenEmbedding.isInducing
    (g.isOpenEmbedding.isOpen_range.isLocallyClosed)
  simpa using this

theorem Scheme.isLocallyClosed_singleton_of_spec (R : CommRingCat.{u}) (p : Spec R)
    (h : LocallyOfFiniteType ((Spec R).fromSpecResidueField p)) :
    IsLocallyClosed ({p} : Set (Spec R)) := by
  haveI := Scheme.finiteType_of_locallyOfFiniteType R p h
  exact isLocallyClosed_singleton_of_finiteType R p.asIdeal

theorem Scheme.isLocallyClosed_singleton_of_affine (Y : Scheme.{u}) [IsAffine Y] (y : Y)
    (h : LocallyOfFiniteType (Y.fromSpecResidueField y)) :
    IsLocallyClosed ({y} : Set Y) := by
  have hinv : Y.isoSpec.inv.base (Y.isoSpec.hom.base y) = y := by
    have : (Y.isoSpec.hom ≫ Y.isoSpec.inv).base y = y := by rw [Y.isoSpec.hom_inv_id]; rfl
    simpa using this
  have h2 : LocallyOfFiniteType
      ((Spec Γ(Y, ⊤)).fromSpecResidueField (Y.isoSpec.hom.base y)) := by
    rw [← Scheme.locallyOfFiniteType_fromSpecResidueField_transport Y.isoSpec.inv (Y.isoSpec.hom.base y), hinv]; exact h
  have h3 := Scheme.isLocallyClosed_singleton_of_spec _ _ h2
  have h4 := Scheme.isLocallyClosed_image_of_isOpenImmersion Y.isoSpec.inv (Y.isoSpec.hom.base y) h3
  rwa [hinv] at h4

theorem Scheme.isLocallyClosed_singleton_forward {X : Scheme.{u}} (x : X)
    (h : LocallyOfFiniteType (X.fromSpecResidueField x)) : IsLocallyClosed ({x} : Set X) := by
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  exact Scheme.isLocallyClosed_image_of_isOpenImmersion (X.affineCover.f i) y
    (Scheme.isLocallyClosed_singleton_of_affine _ y ((Scheme.locallyOfFiniteType_fromSpecResidueField_transport (X.affineCover.f i) y).mp h))

/-- The unnumbered characterization following Definition 4.5.13: let $X$ be a
noetherian scheme and $x \in X$. Then the canonical morphism
$\Spec \kappa(x) \to X$ is locally of finite type — i.e. $x$ is a finite type point of
$X$ — if and only if $\{x\}$ is locally closed in $X$.

The forward implication is proved here by an elementary localization argument rather than
by the book's Generic Flatness: reducing to an affine `Spec R` and to the residue field of
a prime `p`, one shows that a domain whose fraction field is a finite-type algebra over it
admits a single nonzero `b` outside no nonzero prime (`Field`-free, see
`StacksAndModuli/API/FiniteTypeResidueField.lean`), and then `{p}` is cut out of `V(p)` by
inverting `b`. The noetherian hypothesis is not used; it is kept for faithfulness to the
book. See COMMENTARY.md. -/
theorem Scheme.locallyOfFiniteType_fromSpecResidueField_iff_isLocallyClosed
    (X : Scheme.{u}) [IsNoetherian X] (x : X) :
    LocallyOfFiniteType (X.fromSpecResidueField x) ↔ IsLocallyClosed ({x} : Set X) :=
  ⟨Scheme.isLocallyClosed_singleton_forward x, Scheme.isLocallyClosed_singleton_backward x⟩

/- The remaining content of the unlabeled remark after `def:finite-type-point` is prose:
more generally, a finite type morphism `Spec k → X` from a field with image `x` exists
if and only if `{x}` is locally closed and `κ(x)/k` is finite; the generic point of a
DVR is a finite type point that is not closed; for schemes of finite type over a field
every finite type point is closed, while for algebraic stacks this fails — e.g.
`1 : Spec k → [𝔸¹/𝔾ₘ]` is an open finite type point (blocked on quotient stacks,
§3.4/§3.5 ledgers). -/

end AlgebraicGeometry

end DefFiniteTypePoint

section ExerFiniteTypePoints

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.BasedCategory

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} [IsAlgebraicStack 𝒳]

/-- **Exercise 4.5.15** (`exer:finite-type-points`) (part (a)): let $\cX$ be an
algebraic stack. A point $x \in |\cX|$ is of finite type if and only
if there exist a scheme $U$, a closed point $u \in U$, and a smooth morphism
$(U, u) \to (\cX, x)$. -/
theorem isFiniteTypePoint_iff_exists_smooth_isClosed_singleton (x : pointSpace 𝒳) :
    IsFiniteTypePoint 𝒳 x ↔ ∃ (U : Scheme.{u}) (u : U) (F : overBased U ⥤ᵇ 𝒳),
      IsClosed ({u} : Set U) ∧ BasedFunctor.Smooth F ∧
      BasedFunctor.mapPoints F (U.toPointSpace u) = x := by
  sorry

/-- **Exercise 4.5.15** (`exer:finite-type-points`) (part (b), finite type point): every
nonempty algebraic stack has a finite type point. -/
theorem exists_isFiniteTypePoint [Nonempty (pointSpace 𝒳)] :
    ∃ x : pointSpace 𝒳, IsFiniteTypePoint 𝒳 x := by
  sorry

/-- **Exercise 4.5.15** (`exer:finite-type-points`) (part (b), closed point): every
nonempty quasi-compact algebraic stack has a closed point. -/
theorem exists_isClosed_singleton_of_isQuasiCompact [Nonempty (pointSpace 𝒳)]
    (hqc : IsQuasiCompact 𝒳) :
    ∃ x : pointSpace 𝒳, IsClosed ({x} : Set (pointSpace 𝒳)) := by
  sorry

end AlgebraicGeometry.BasedCategory

end ExerFiniteTypePoints

section PropResidualGerbeAlgebraic

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ u₂ v₃ u₃ v₄ u₄ u

namespace AlgebraicGeometry.BasedCategory

/-- **Proposition 4.5.16** (`prop:residual-gerbe-algebraic`) (existence of residual
gerbes): let $\cX$ be a noetherian algebraic stack —
spelled here as locally noetherian and quasi-compact; the quasi-separatedness of the
noetherian condition requires the §4.2 diagonal and is not recorded, see COMMENTARY.md —
and let
$x \in |\cX|$ be a finite type point. Then the residual gerbe at $x$ exists. -/
theorem hasResidualGerbeAt_of_isFiniteTypePoint {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}
    [IsAlgebraicStack 𝒳] (hln : IsLocallyNoetherian 𝒳) (hqc : IsQuasiCompact 𝒳)
    {x : pointSpace 𝒳} (hx : IsFiniteTypePoint 𝒳 x) : HasResidualGerbeAt 𝒳 x := by
  sorry

end AlgebraicGeometry.BasedCategory

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒢 : BasedCategory.{v₃, u₃} Scheme.{u}}
  {𝒢' : BasedCategory.{v₄, u₄} Scheme.{u}} [IsAlgebraicStack 𝒳]

/-- **Proposition 4.5.16** (`prop:residual-gerbe-algebraic`) (uniqueness of residual
gerbes): let $\cX$ be a noetherian algebraic stack (locally
noetherian and quasi-compact) and $x \in |\cX|$ a finite type point. Any two residual
gerbes at $x$ are equivalent over $\cX$: there is an equivalence $E \colon \cG \to \cG'$
of prestacks together with a 2-isomorphism between the composition $\cG \to \cG' \to \cX$
and the inclusion $\cG \to \cX$. -/
theorem IsResidualGerbeAt.exists_isEquivalence
    (hln : BasedCategory.IsLocallyNoetherian 𝒳) (hqc : BasedCategory.IsQuasiCompact 𝒳)
    {x : pointSpace 𝒳} (hx : BasedCategory.IsFiniteTypePoint 𝒳 x) {F : 𝒢 ⥤ᵇ 𝒳}
    {F' : 𝒢' ⥤ᵇ 𝒳} (h : IsResidualGerbeAt F x) (h' : IsResidualGerbeAt F' x) :
    ∃ E : 𝒢 ⥤ᵇ 𝒢', E.toFunctor.IsEquivalence ∧ Nonempty (E.comp F' ≅ F) := by
  sorry

/-- **Proposition 4.5.16** (`prop:residual-gerbe-algebraic`) (part (1), the locally
closed immersion half): let $\cX$ be a noetherian algebraic stack (locally noetherian
and quasi-compact) and
$x \in |\cX|$ a finite type point. Then the inclusion of a residual gerbe at $x$ is a
locally closed immersion. (The regularity of the residual gerbe, the other half of
part (1), is deferred: Mathlib has no class of regular
schemes, so regular algebraic stacks are not yet available — see the §4.3 ledger.) -/
theorem IsResidualGerbeAt.isLocallyClosedSubstackInclusion
    (hln : BasedCategory.IsLocallyNoetherian 𝒳) (hqc : BasedCategory.IsQuasiCompact 𝒳)
    {x : pointSpace 𝒳} (hx : BasedCategory.IsFiniteTypePoint 𝒳 x) {F : 𝒢 ⥤ᵇ 𝒳}
    (h : IsResidualGerbeAt F x) : IsLocallyClosedSubstackInclusion F := by
  sorry

/- LEDGER (Proposition 4.5.16, part (2)): if in
addition `𝒳` is of finite type
over a field `k` and `x ∈ 𝒳(k)` has a smooth affine stabilizer `G_x`, then
The residual gerbe is equivalent to `B G_x`. This is blocked on stabilizer group schemes
(§4.2 inertia and Exercise 3.4.39), classifying stacks `BG` and their stackification
(§3.4/§3.5 ledgers), and
monomorphisms of prestacks induced under stackification. -/

/-- **Proposition 4.5.16** (`prop:residual-gerbe-algebraic`) (part (3)): let $\cX$ be a
noetherian algebraic space — a prestack represented by an
algebraic-space presheaf, locally noetherian and quasi-compact — and $x \in |\cX|$ a
finite type point. Then any residual gerbe at $x$ is represented by the spectrum of a
field $\kappa(x)$, the *residue field* of $x$. -/
theorem IsResidualGerbeAt.exists_field_isRepresentedBy_spec
    (hsp : ∃ X : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace X ∧ 𝒳.IsRepresentedByPresheaf X)
    (hln : BasedCategory.IsLocallyNoetherian 𝒳) (hqc : BasedCategory.IsQuasiCompact 𝒳)
    {x : pointSpace 𝒳} (hx : BasedCategory.IsFiniteTypePoint 𝒳 x) {F : 𝒢 ⥤ᵇ 𝒳}
    (h : IsResidualGerbeAt F x) :
    ∃ (K : Type u) (_ : Field K), 𝒢.IsRepresentedBy (Spec (CommRingCat.of K)) := by
  sorry

end AlgebraicGeometry.BasedFunctor

end PropResidualGerbeAlgebraic

section ExerDim0AlgebraicSpace

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe u

/-- **Exercise 4.5.17** (`exer:dim-0-algebraic-space`): let $X$ be a reduced noetherian
algebraic space (locally noetherian and
quasi-compact) such that $|X|$ is a single point. Then $X \cong \Spec k$ for a field
$k$. -/
theorem AlgebraicGeometry.IsAlgebraicSpace.exists_field_iso_yoneda_spec
    (X : Scheme.{u}ᵒᵖ ⥤ Type u) [IsAlgebraicSpace X]
    (hred : BasedCategory.IsReduced (ofPresheaf X))
    (hln : BasedCategory.IsLocallyNoetherian (ofPresheaf X))
    (hqc : IsQuasiCompact (ofPresheaf X)) [Nonempty (pointSpace (ofPresheaf X))]
    (hpt : Subsingleton (pointSpace (ofPresheaf X))) :
    ∃ (K : Type u) (_ : Field K),
      Nonempty (X ≅ yoneda.obj (Spec (CommRingCat.of K))) := by
  sorry

end ExerDim0AlgebraicSpace

section ExerNonNoetherianResidualGerbesDM

/- LEDGER (**Exercise 4.5.18**, `exer:non-noetherian-residual-gerbes-DM`): for a
possibly non-noetherian
algebraic stack `𝒳` and a finite type point `x ∈ |𝒳|` whose stabilizer is unramified
(the stabilizer group scheme of any representative is unramified), the residual gerbe at
`x` exists and is unique (cf. Stacks 06G3). Blocked on stabilizer group schemes (§4.2
inertia, `exer:isom-presheaf` §3.4 ledger) and on a bundled `Unramified` class for
morphisms of schemes (Mathlib has only `FormallyUnramified`; unramifiedness is spelled
`@LocallyOfFiniteType ⊓ @FormallyUnramified` in §4.3, but a group-scheme-level notion is
needed here). -/

end ExerNonNoetherianResidualGerbesDM

section RmkOrbitCartesianDiagram

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒢 : BasedCategory.{v₃, u₃} Scheme.{u}}
  [IsAlgebraicStack 𝒳]

/-- The unlabelled corollary before Remark 4.5.21, anchored at Equation 4.5.20: let
`𝒳` be a noetherian algebraic stack (locally noetherian and quasi-compact), `x ∈ |𝒳|` a
finite type point, `𝒢 → 𝒳` a residual gerbe at `x`, and `(U, u) → (𝒳, x)` a smooth
morphism from a scheme carrying a finite type point `u` over `x`. Then the fiber product
`𝒢 ×_𝒳 U` is represented by a locally closed subscheme `O(u) ⊆ U` — a scheme `O` with an
immersion `j : O → U` inducing the second projection.

The book adds that `O(u)` is set-theoretically the orbit `s(t⁻¹(u))` of the groupoid
`s, t : U ×_𝒳 U ⇉ U` induced by the presentation. That clause is not stated: the induced
groupoid of a presentation is the content of the unnumbered exercise in §4.4,
`exists_isStackification_quotientPrestack_of_presentation`, itself deferred), and the
orbit of a point under it is `AlgebraicGeometry.groupoidOrbit`, defined only for groupoids
of *schemes*. See COMMENTARY.md. -/
theorem IsResidualGerbeAt.exists_isImmersion_isRepresentedBy_fiberProduct
    (hln : BasedCategory.IsLocallyNoetherian 𝒳) (hqc : BasedCategory.IsQuasiCompact 𝒳)
    {x : pointSpace 𝒳} (hx : BasedCategory.IsFiniteTypePoint 𝒳 x) {F : 𝒢 ⥤ᵇ 𝒳}
    (h : IsResidualGerbeAt F x) {U : Scheme.{u}} (p : overBased U ⥤ᵇ 𝒳)
    (hp : BasedFunctor.Smooth p) (u : U)
    (hu : BasedCategory.IsFiniteTypePoint (overBased U) (U.toPointSpace u))
    (hux : BasedFunctor.mapPoints p (U.toPointSpace u) = x) :
    ∃ (O : Scheme.{u}) (j : O ⟶ U), IsImmersion j ∧
      ∃ E : overBased O ⥤ᵇ BasedCategory.fiberProduct F p, E.toFunctor.IsEquivalence ∧
        Nonempty (E.comp (BasedCategory.fiberProductSnd F p) ≅ overBased.map j) := by
  sorry

end AlgebraicGeometry.BasedFunctor

/- LEDGER (the set-theoretic half of the same corollary): `O(u)` is the orbit `s(t⁻¹(u))`
of the induced groupoid `s, t : U ×_𝒳 U ⇉ U`; it needs the groupoid of a presentation
(§4.4, `exists_isStackification_quotientPrestack_of_presentation`) and an orbit notion for
groupoids of algebraic spaces.

LEDGER (**Remark 4.5.21**, `rmk:orbit-cartesian-diagram`): for `𝒳 = [U/G]` a quotient
stack of a smooth
affine algebraic group over a field acting on a noetherian scheme `U` and `u ∈ U(k)`,
the cartesian diagram identifies `Gu ≅ 𝒢_x ×_{[U/G]} U`, recovering that orbits are
locally closed (`prop:affine-algebraic-group`). Blocked on quotient stacks `[U/G]` and
classifying stacks `BG` (§3.4/§3.5 ledgers). -/

end RmkOrbitCartesianDiagram

section ExerDimensionOfResidualGerbe

/- LEDGER (**Exercise 4.5.22**, `exer:dimension-of-residual-gerbe`): for a noetherian
algebraic stack `𝒳` and
a finite type point `x ∈ |𝒳|` with smooth stabilizer, with representative
`x̄ : Spec k → 𝒳`, the residual gerbe satisfies `dim 𝒢_x = -dim G_x̄`. Blocked on
stabilizer group schemes (§4.2 inertia), classifying stacks `BG`, and `ex:dimension`
(`dim BG = -dim G`, part 4.5.1 ledger). -/

end ExerDimensionOfResidualGerbe
