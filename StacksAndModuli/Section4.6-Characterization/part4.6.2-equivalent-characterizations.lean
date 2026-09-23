module

public import StacksAndModuli.«Section4.6-Characterization».«part4.6.1-existence-of-minimal-presentations»
public import StacksAndModuli.«Section4.2-Representability».«part4.2.2-stabilizers»
public import StacksAndModuli.«Section4.3-Properties».«part4.3.6-etale-and-unramified»
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.4-algebraicity-of-mg»
public import StacksAndModuli.«Section4.5-Dimension».«part4.5.2-tangent-spaces»
public import StacksAndModuli.«Section4.4-Equivalence-Relations».«part4.4.4-algebraicity»
public import StacksAndModuli.API.PresentationBaseChange
public import StacksAndModuli.API.QuasiCompactUnramifiedSchemeModel
public import StacksAndModuli.API.RelativelyRepresentableMonomorphism
public import StacksAndModuli.API.RepresentableWithEquivalence
public import StacksAndModuli.API.SmoothFullyFaithfulOpenImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Equivalent characterizations of algebraic spaces and Deligne–Mumford stacks

This module formalizes `thm:characterization-of-DM-stacks` (Theorem 4.6.4),
`cor:characterization-of-relatively-DM` (Corollary 4.6.5),
`thm:characterization-of-algebraic-spaces` (Theorem 4.6.6) and
`cor:characterization-of-representable-morphisms` (Corollary 4.6.9), and records
`cor:quotient-stacks-are-dm` (Corollary 4.6.8) and `cor:mg-is-dm` (Corollary 4.6.10) as
LEDGER entries — the subsection "Equivalent characterizations" of §4.6 (Characterization
of Deligne–Mumford stacks) of *Stacks and Moduli*
(neither the section nor its subsections carries a
`sec:` label).

Unramifiedness of a morphism of schemes is spelled
`@LocallyOfFiniteType ⊓ @FormallyUnramified` throughout (Mathlib has no bundled
`Unramified` class); over a field it amounts to the source being discrete and
(geometrically) reduced, which renders the book's stabilizer conditions.

Main results (all in the `AlgebraicGeometry` namespace):
- `IsAlgebraicStack.isDeligneMumfordStack_iff_representableWith_unramified_diag`,
  `IsAlgebraicStack.representableWith_unramified_diag_iff_unramified_stabilizer` and
  `IsAlgebraicStack.representableWith_unramified_stabilizer_iff_isFinite_of_quasiCompact_diag`:
  the Characterization of Deligne–Mumford Stacks — an algebraic stack is Deligne–Mumford
  if and only if its diagonal is unramified, if and only if all its stabilizers are
  discrete and reduced (finite and reduced when the diagonal is quasi-compact);
- `BasedFunctor.relativelyDeligneMumford_iff_representableWith_unramified_diag`: a
  morphism of algebraic stacks is relatively Deligne–Mumford if and only if its relative
  diagonal is unramified;
- `IsAlgebraicStack.exists_isAlgebraicSpace_iff_relativelyRepresentableWith_monomorphisms_diag`,
  `IsAlgebraicStack.relativelyRepresentableWith_monomorphisms_diag_iff_isomorphisms_stabilizer`:
  the Characterization of Algebraic Spaces — an algebraic stack with diagonal representable
  by schemes is an algebraic space if and only if its diagonal is a monomorphism, if and
  only if all its stabilizers are trivial;
- `BasedFunctor.representable_iff_injective_isoWhiskerRight`: the Characterization of
  Representable Morphisms via injectivity on automorphism groups of geometric points.

**Corollary 4.6.10** (`cor:mg-is-dm`) is stated here — `ℳ_g` is a Deligne–Mumford stack, of
finite type over `ℤ`, with affine diagonal — now that `ℳ_g` itself exists
(`AlgebraicGeometry.Scheme.moduliOfCurves`, §4.1 part4.1.4). Its proof is a recorded
obligation: it needs `H⁰(C, T_C) = 0` for `g ≥ 2`, hence the tangent sheaf of a curve, and
first-order deformation theory (Appendix C.2).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ThmCharacterizationOfDMStacks

open CategoryTheory Functor Limits

universe v₂ u₂ u

namespace AlgebraicGeometry

open CategoryTheory.BasedCategory

variable (𝒳 : CategoryTheory.BasedCategory.{v₂, u₂} Scheme.{u}) [IsAlgebraicStack 𝒳]

omit [IsAlgebraicStack 𝒳] in
/-- Supporting forward implication for Theorem 4.6.4: a Deligne–Mumford algebraic stack
has unramified diagonal. This restates Exercise 4.2.8
with the conjunction in the order used in this section. -/
theorem IsAlgebraicStack.representableWith_unramified_diag_of_isDeligneMumfordStack
    (h𝒳 : IsDeligneMumfordStack 𝒳) :
    BasedFunctor.RepresentableWith
      (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u})
      (BasedCategory.diag 𝒳) := by
  let _ : IsDeligneMumfordStack 𝒳 := h𝒳
  have hswap :
      (@FormallyUnramified ⊓ @LocallyOfFiniteType : MorphismProperty Scheme.{u}) ≤
        (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u}) := by
    intro X Y f h
    exact ⟨h.2, h.1⟩
  exact BasedFunctor.RepresentableWith.mono hswap
    (IsDeligneMumfordStack.representableWith_unramified_diag 𝒳)

/-- **Theorem 4.6.4** (`thm:characterization-of-DM-stacks`) ((1) ↔ (2), Characterization
of Deligne–Mumford Stacks): an algebraic stack $\cX$ is a Deligne–Mumford stack if and
only if its diagonal $\Delta \colon \cX \to \cX \times \cX$ is unramified: the diagonal is
representable, and on étale presentations of its base changes to schemes it is locally of
finite type and formally unramified. (Mathlib has no bundled `Unramified` class for
morphisms of schemes, so unramifiedness is spelled
`@LocallyOfFiniteType ⊓ @FormallyUnramified`; this property is stable under base change
and étale local on the source, so the notion is well defined for representable
morphisms — see COMMENTARY.md.) The forward implication is
Exercise 4.2.8; the converse rests on the Existence of Minimal Presentations (Theorem
4.6.1, ledgered
in part 4.6.1). -/
theorem IsAlgebraicStack.isDeligneMumfordStack_iff_representableWith_unramified_diag :
    IsDeligneMumfordStack 𝒳 ↔
      BasedFunctor.RepresentableWith
        (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u})
        (BasedCategory.diag 𝒳) := by
  constructor
  · exact IsAlgebraicStack.representableWith_unramified_diag_of_isDeligneMumfordStack 𝒳
  · sorry

omit [IsAlgebraicStack 𝒳] in
/-- Supporting forward implication for Theorem 4.6.4: an unramified diagonal has
unramified stabilizers, because each stabilizer projection is a
base change of the diagonal. -/
theorem IsAlgebraicStack.representableWith_unramified_stabilizer_of_diag
    (h : BasedFunctor.RepresentableWith
      (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u})
      (BasedCategory.diag 𝒳)) (K : Type u) [Field K]
    (x : overBased (Spec (CommRingCat.of K)) ⥤ᵇ 𝒳) :
    BasedFunctor.RepresentableWith
      (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u})
      (fiberProductSnd (BasedCategory.diag 𝒳) (prodLift x x)) :=
  h.fiberProductSnd (prodLift x x)

/-- **Theorem 4.6.4** (`thm:characterization-of-DM-stacks`) ((2) ↔ (3)): let $\cX$ be an
algebraic stack. The diagonal $\Delta \colon \cX \to \cX \times \cX$ is unramified if and
only if for every field $K$ and point $x \colon \Spec K \to \cX$ the stabilizer projection
$G_x \to \Spec K$ is unramified. Since a morphism which is locally of finite type over a
field is unramified precisely when its source is discrete with geometrically reduced
(spectra of finite separable extension) fibers, this is the book's condition that every
point of $\cX$ has a discrete and reduced stabilizer group; the diagonal is automatically
locally of finite type (Exercise 4.3.5), and its
fibers over field-valued points are either empty or stabilizers. -/
theorem IsAlgebraicStack.representableWith_unramified_diag_iff_unramified_stabilizer :
    BasedFunctor.RepresentableWith
        (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u})
        (BasedCategory.diag 𝒳) ↔
      ∀ (K : Type u) [Field K] (x : overBased (Spec (CommRingCat.of K)) ⥤ᵇ 𝒳),
        BasedFunctor.RepresentableWith
          (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u})
          (fiberProductSnd (BasedCategory.diag 𝒳) (prodLift x x)) := by
  constructor
  · exact IsAlgebraicStack.representableWith_unramified_stabilizer_of_diag 𝒳
  · sorry

/-- Supporting implication for the quasi-compact-diagonal addendum to Theorem 4.6.4: a
finite formally unramified scheme representative of
a stabilizer makes that stabilizer unramified in the stack-theoretic sense. -/
theorem IsAlgebraicStack.representableWith_unramified_stabilizer_of_finite_representation
    {K : Type u} [Field K] (x : overBased (Spec (CommRingCat.of K)) ⥤ᵇ 𝒳)
    (G : Scheme.{u}) (E : overBased G ⥤ᵇ BasedCategory.stabilizer x)
    (hE : E.toFunctor.IsEquivalence)
    (hfinite : IsFinite
      (E.comp (fiberProductSnd (BasedCategory.diag 𝒳) (prodLift x x))).overHom)
    (hunramified : FormallyUnramified
      (E.comp (fiberProductSnd (BasedCategory.diag 𝒳) (prodLift x x))).overHom) :
    BasedFunctor.RepresentableWith
      (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u})
      (fiberProductSnd (BasedCategory.diag 𝒳) (prodLift x x)) := by
  let H := fiberProductSnd (BasedCategory.diag 𝒳) (prodLift x x)
  have hP :
      (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u})
        (E.comp H).overHom := by
    let _ : IsFinite (E.comp H).overHom := hfinite
    exact ⟨inferInstance, hunramified⟩
  have hrelative :
      (E.comp H).RelativelyRepresentableWith
        (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u}) :=
    BasedFunctor.relativelyRepresentableWith_of_overHom (E.comp H) hP
  have hetale :
      (@Surjective ⊓ @Etale : MorphismProperty Scheme.{u}) ≤
        (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u}) := by
    intro X Y f hf
    let _ : Etale f := hf.2
    exact ⟨inferInstance, inferInstance⟩
  have hrepresented :
      BasedFunctor.RepresentableWith
        (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u})
        (E.comp H) :=
    BasedFunctor.RelativelyRepresentableWith.representableWith hetale hrelative
  let _ : E.toFunctor.IsEquivalence := hE
  simpa only [H] using
    BasedFunctor.RepresentableWith.of_comp_isEquivalence E hrepresented

/-- The unnumbered quasi-compact-diagonal addendum to Theorem 4.6.4: let
$\cX$ be an algebraic stack with quasi-compact diagonal (for example a quasi-separated
algebraic stack). The stabilizer projection $G_x \to \Spec K$ of a field-valued point
$x \colon \Spec K \to \cX$ is unramified if and only if it is finite and formally
unramified, i.e. the stabilizer is finite and reduced. This upgrades condition (3) of the
Characterization of Deligne–Mumford Stacks from "discrete and reduced" to "finite and
reduced" stabilizers.

Finiteness is deliberately expressed by the existence of a finite scheme representative,
not by `RepresentableWith IsFinite`: the latter tests every surjective étale presentation
of an algebraic-space fiber, and finiteness is not étale-local on the source. -/
theorem IsAlgebraicStack.representableWith_unramified_stabilizer_iff_isFinite_of_quasiCompact_diag
    (hqc : BasedFunctor.QuasiCompact (BasedCategory.diag 𝒳)) {K : Type u} [Field K]
    (x : overBased (Spec (CommRingCat.of K)) ⥤ᵇ 𝒳) :
    BasedFunctor.RepresentableWith
        (@LocallyOfFiniteType ⊓ @FormallyUnramified : MorphismProperty Scheme.{u})
        (fiberProductSnd (BasedCategory.diag 𝒳) (prodLift x x)) ↔
      ∃ (G : Scheme.{u})
        (E : overBased G ⥤ᵇ BasedCategory.stabilizer x),
        E.toFunctor.IsEquivalence ∧
          IsFinite
            (E.comp (fiberProductSnd (BasedCategory.diag 𝒳) (prodLift x x))).overHom ∧
          FormallyUnramified
            (E.comp (fiberProductSnd (BasedCategory.diag 𝒳) (prodLift x x))).overHom := by
  constructor
  · intro hunramified
    let H := fiberProductSnd (BasedCategory.diag 𝒳) (prodLift x x)
    have hHqc : BasedFunctor.QuasiCompact H :=
      hqc.fiberProductSnd (prodLift x x)
    obtain ⟨A, hA, hArep⟩ :=
      IsAlgebraicStack.exists_isAlgebraicSpace_stabilizer 𝒳 x
    obtain ⟨G, E, hE⟩ :
        ∃ (G : Scheme.{u}) (E : overBased G ⥤ᵇ BasedCategory.stabilizer x),
          E.toFunctor.IsEquivalence := by
      sorry
    have hproperties :=
      hunramified.isFinite_of_quasiCompact_scheme_representation_over_field
        hHqc G E hE
    exact ⟨G, E, hE, hproperties.1, hproperties.2⟩
  · rintro ⟨G, E, hE, hfinite, hunramified⟩
    exact IsAlgebraicStack.representableWith_unramified_stabilizer_of_finite_representation
      𝒳 x G E hE hfinite hunramified

end AlgebraicGeometry

end ThmCharacterizationOfDMStacks

section CorCharacterizationOfRelativelyDM

open CategoryTheory Functor Limits

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

open CategoryTheory.BasedCategory

variable {𝒳 : CategoryTheory.BasedCategory.{v₂, u₂} Scheme.{u}}
  {𝒴 : CategoryTheory.BasedCategory.{v₃, u₃} Scheme.{u}} [IsAlgebraicStack 𝒳]
  [IsAlgebraicStack 𝒴]

/-- **Corollary 4.6.5** (`cor:characterization-of-relatively-DM`): a morphism
$F \colon \cX \to \cY$ of algebraic stacks is relatively Deligne–Mumford (all its base
changes by schemes are Deligne–Mumford stacks, Definition 4.3.36) if and only if its
relative diagonal
$\Delta_F \colon \cX \to \cX \times_{\cY} \cX$ is unramified, i.e. representable with the
property of being locally of finite type and formally unramified. -/
theorem relativelyDeligneMumford_iff_representableWith_unramified_diag (F : 𝒳 ⥤ᵇ 𝒴) :
    RelativelyDeligneMumford F ↔
      RepresentableWith
        (@_root_.AlgebraicGeometry.LocallyOfFiniteType ⊓
          @_root_.AlgebraicGeometry.FormallyUnramified : MorphismProperty Scheme.{u})
        F.diag := by
  sorry

end AlgebraicGeometry.BasedFunctor

end CorCharacterizationOfRelativelyDM

section ThmCharacterizationOfAlgebraicSpaces

open CategoryTheory Functor Limits

universe v₂ u₂ u

namespace AlgebraicGeometry

open CategoryTheory.BasedCategory

variable (𝒳 : CategoryTheory.BasedCategory.{v₂, u₂} Scheme.{u}) [IsAlgebraicStack 𝒳]

/-- Supporting bridge in the proof of Theorem 4.6.6: let $\cX$ be an algebraic stack in
which every endomorphism of an object lying
over an identity is the identity, i.e. $\cX$ is fibered in setoids. Then $\cX$ is
(represented by) an algebraic space. (A category fibered in setoids is equivalent to the
prestack associated to its presheaf of isomorphism classes, whose sheaf condition and
étale presentation are inherited from $\cX$; this replaces the book's appeal to the
unformalized `Isom` presheaves of Exercise 3.4.39 — see
COMMENTARY.md.) -/
theorem IsAlgebraicStack.exists_isAlgebraicSpace_of_forall_isHomLift_eq_id
    (h : ∀ (a : 𝒳.obj) (φ : a ⟶ a), IsHomLift 𝒳.p (𝟙 (𝒳.p.obj a)) φ → φ = 𝟙 a) :
    ∃ X : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace X ∧ 𝒳.IsRepresentedByPresheaf X := by
  sorry

/-- **Theorem 4.6.6** (`thm:characterization-of-algebraic-spaces`) ((1) ↔ (2),
Characterization of Algebraic Spaces): let $\cX$ be an algebraic stack whose diagonal
$\Delta \colon \cX \to \cX \times \cX$ is representable by schemes. Then $\cX$ is an
algebraic space (it is represented by a presheaf which is an algebraic space) if and only
if the diagonal is a monomorphism, i.e. every base change of $\Delta$ by a morphism from a
scheme is a monomorphism of schemes. The forward implication follows from the definition
of an algebraic space; the converse rests on the Existence of Minimal Presentations
(Theorem 4.6.1, ledgered in part 4.6.1). -/
theorem IsAlgebraicStack.exists_isAlgebraicSpace_iff_relativelyRepresentableWith_monomorphisms_diag
    (hdiag : (BasedCategory.diag 𝒳).RelativelyRepresentable) :
    (∃ X : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace X ∧ 𝒳.IsRepresentedByPresheaf X) ↔
      (BasedCategory.diag 𝒳).RelativelyRepresentableWith
        (MorphismProperty.monomorphisms Scheme.{u}) := by
  constructor
  · rintro ⟨X, hX, E, hE⟩
    let _ : E.toFunctor.IsEquivalence := hE
    have hp : 𝒳.p.Faithful :=
      projection_faithful_of_equivalence_from_ofPresheaf E
    let _ : 𝒳.p.Faithful := hp
    have hfull : (BasedCategory.diag 𝒳).toFunctor.Full :=
      diag_full_of_projection_faithful (𝒳 := 𝒳)
    have hfaithful : (BasedCategory.diag 𝒳).toFunctor.Faithful :=
      diag_faithful (𝒳 := 𝒳)
    let _ : (BasedCategory.diag 𝒳).toFunctor.Full := hfull
    let _ : (BasedCategory.diag 𝒳).toFunctor.Faithful := hfaithful
    exact BasedFunctor.relativelyRepresentableWith_monomorphisms_of_full_faithful hdiag
  · intro hmono
    have hfull : (BasedCategory.diag 𝒳).toFunctor.Full :=
      hmono.toFunctor_full_of_monomorphisms
    have hfaithful : (BasedCategory.diag 𝒳).toFunctor.Faithful :=
      diag_faithful (𝒳 := 𝒳)
    have hp : 𝒳.p.Faithful :=
      diag_isMonomorphism_iff_projection_faithful.mp ⟨hfull, hfaithful⟩
    let _ : 𝒳.p.Faithful := hp
    apply IsAlgebraicStack.exists_isAlgebraicSpace_of_forall_isHomLift_eq_id 𝒳
    intro a φ hφ
    apply 𝒳.p.map_injective
    exact (IsHomLift.eq_of_isHomLift 𝒳.p (𝟙 (𝒳.p.obj a)) φ).symm.trans
      (𝒳.p.map_id a).symm

/-- **Theorem 4.6.6** (`thm:characterization-of-algebraic-spaces`) ((2) ↔ (3)): let $\cX$
be an algebraic stack whose diagonal $\Delta \colon \cX \to \cX \times \cX$ is
representable by schemes. Then the diagonal is a monomorphism if and only if for every
field $K$ and point $x \colon \Spec K \to \cX$ the stabilizer projection
$G_x \to \Spec K$ is an isomorphism, i.e. every point of $\cX$ has trivial stabilizer.
(The proof uses that a group scheme of finite type is trivial if and only if every fiber
is trivial, Proposition B.1.9.) -/
theorem IsAlgebraicStack.relativelyRepresentableWith_monomorphisms_diag_iff_isomorphisms_stabilizer
    (hdiag : (BasedCategory.diag 𝒳).RelativelyRepresentable) :
    (BasedCategory.diag 𝒳).RelativelyRepresentableWith
        (MorphismProperty.monomorphisms Scheme.{u}) ↔
      ∀ (K : Type u) [Field K] (x : overBased (Spec (CommRingCat.of K)) ⥤ᵇ 𝒳),
        (fiberProductSnd (BasedCategory.diag 𝒳) (prodLift x x)).RelativelyRepresentableWith
          (MorphismProperty.isomorphisms Scheme.{u}) := by
  sorry

/- The unlabeled remark following **Theorem 4.6.6** (`thm:characterization-of-algebraic-spaces`):
the hypothesis that the diagonal `Δ_𝒳` is representable by schemes will be removed in
`thm:characterization-of-algebraic-spacesII` (Theorem 5.5.10); forward reference, not
formalized here. (The remark carries no label; the numbering gap 4.6.6 → 4.6.8 in the
compiled book indicates it is Remark 4.6.7 — see COMMENTARY.md.) -/

end AlgebraicGeometry

end ThmCharacterizationOfAlgebraicSpaces

section CorQuotientStacksAreDm

open CategoryTheory Limits Opposite AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ u

namespace AlgebraicGeometry.PresheafGroupoid

variable {S G U₀ : Scheme.{u}} (πG : G ⟶ S) (πU : U₀ ⟶ S) (m : pullback πG πG ⟶ G)
  (eG : S ⟶ G) (ι : G ⟶ G) (σ : pullback πG πU ⟶ U₀)

variable (hm : m ≫ πG = pullback.fst πG πG ≫ πG) (heG : eG ≫ πG = 𝟙 S)
  (hι : ι ≫ πG = πG) (hσ : σ ≫ πU = pullback.snd πG πU ≫ πU)

variable (hm_assoc : ∀ {T : Scheme.{u}} (g₁ g₂ g₃ : T ⟶ G) (h₁₂ : g₁ ≫ πG = g₂ ≫ πG)
    (h₂₃ : g₂ ≫ πG = g₃ ≫ πG) (h₁ : (pullback.lift g₁ g₂ h₁₂ ≫ m) ≫ πG = g₃ ≫ πG)
    (h₂ : g₁ ≫ πG = (pullback.lift g₂ g₃ h₂₃ ≫ m) ≫ πG),
    pullback.lift (pullback.lift g₁ g₂ h₁₂ ≫ m) g₃ h₁ ≫ m =
      pullback.lift g₁ (pullback.lift g₂ g₃ h₂₃ ≫ m) h₂ ≫ m)

variable (hm_one_mul : ∀ {T : Scheme.{u}} (g : T ⟶ G)
    (h : (g ≫ πG ≫ eG) ≫ πG = g ≫ πG), pullback.lift (g ≫ πG ≫ eG) g h ≫ m = g)

variable (hm_mul_one : ∀ {T : Scheme.{u}} (g : T ⟶ G)
    (h : g ≫ πG = (g ≫ πG ≫ eG) ≫ πG), pullback.lift g (g ≫ πG ≫ eG) h ≫ m = g)

variable (hm_inv_mul : ∀ {T : Scheme.{u}} (g : T ⟶ G) (h : (g ≫ ι) ≫ πG = g ≫ πG),
    pullback.lift (g ≫ ι) g h ≫ m = g ≫ πG ≫ eG)

variable (hm_mul_inv : ∀ {T : Scheme.{u}} (g : T ⟶ G) (h : g ≫ πG = (g ≫ ι) ≫ πG),
    pullback.lift g (g ≫ ι) h ≫ m = g ≫ πG ≫ eG)

variable (hσ_mul : ∀ {T : Scheme.{u}} (g' g : T ⟶ G) (u : T ⟶ U₀)
    (hg : g' ≫ πG = g ≫ πG) (hu : g ≫ πG = u ≫ πU)
    (h₁ : (pullback.lift g' g hg ≫ m) ≫ πG = u ≫ πU)
    (h₂ : g' ≫ πG = (pullback.lift g u hu ≫ σ) ≫ πU),
    pullback.lift (pullback.lift g' g hg ≫ m) u h₁ ≫ σ =
      pullback.lift g' (pullback.lift g u hu ≫ σ) h₂ ≫ σ)

variable (hσ_one : ∀ {T : Scheme.{u}} (u : T ⟶ U₀)
    (h : (u ≫ πU ≫ eG) ≫ πG = u ≫ πU), pullback.lift (u ≫ πU ≫ eG) u h ≫ σ = u)

/-- **Corollary 4.6.8** (`cor:quotient-stacks-are-dm`) (part (1)): let `G → S` be a smooth
affine group scheme acting on an `S`-scheme `U`, and let `𝒳 = [U/G]` be a stackification of
the quotient prestack of the action groupoid (Example 4.4.3).
Then `𝒳` is Deligne–Mumford if and only if the action map
`(g, u) ↦ (g·u, u) : G ×_S U → U ×_S U` (`actionMap`) is unramified, i.e. locally of finite
type and formally unramified.

The book's first formulation — `[U/G]` is Deligne–Mumford if and only if every point of `U`
has a *discrete and reduced* stabilizer group — is the same condition read fiberwise, and is
not stated here: it needs the stabilizer *group schemes* of the points of `U`, which are
part of the §4.2.2 ledger (the unlabelled remark after Definition 4.2.15). See
COMMENTARY.md. -/
theorem isDeligneMumfordStack_quotientPrestack_ofAction_iff_unramified_actionMap
    [Smooth πG] [IsAffineHom πG] {𝒳st : BasedCategory.{v₂, u₂} Scheme.{u}}
    {i : (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
      hm_inv_mul hm_mul_inv hσ_mul hσ_one).quotientPrestack ⥤ᵇ 𝒳st}
    (hi : i.IsStackification Scheme.etaleTopology) :
    IsDeligneMumfordStack 𝒳st ↔
      (_root_.AlgebraicGeometry.LocallyOfFiniteType (actionMap πG πU σ hσ) ∧
        _root_.AlgebraicGeometry.FormallyUnramified (actionMap πG πU σ hσ)) := by
  sorry

/-- **Corollary 4.6.8** (`cor:quotient-stacks-are-dm`) (part (2)): in the same situation,
`𝒳 = [U/G]` is an algebraic space — it is represented by a presheaf which is an algebraic
space, the reading of Theorem 4.6.6 — if and
only if the action map `G ×_S U → U ×_S U` is a monomorphism.

As in part (1), the book's equivalent formulation "every point of `U` has trivial
stabilizer group" is left to prose pending the stabilizer group schemes of §4.2.2. -/
theorem exists_isAlgebraicSpace_quotientPrestack_ofAction_iff_mono_actionMap
    [Smooth πG] [IsAffineHom πG] {𝒳st : BasedCategory.{v₂, u₂} Scheme.{u}}
    {i : (ofAction πG πU m eG ι σ hm heG hι hσ hm_assoc hm_one_mul hm_mul_one
      hm_inv_mul hm_mul_inv hσ_mul hσ_one).quotientPrestack ⥤ᵇ 𝒳st}
    (hi : i.IsStackification Scheme.etaleTopology) :
    (∃ X : Scheme.{u}ᵒᵖ ⥤ Type u, IsAlgebraicSpace X ∧ 𝒳st.IsRepresentedByPresheaf X) ↔
      Mono (actionMap πG πU σ hσ) := by
  sorry

end AlgebraicGeometry.PresheafGroupoid

end CorQuotientStacksAreDm

section CorCharacterizationOfRepresentableMorphisms

open CategoryTheory Functor Limits

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

open CategoryTheory.BasedCategory

variable {𝒳 : CategoryTheory.BasedCategory.{v₂, u₂} Scheme.{u}}
  {𝒴 : CategoryTheory.BasedCategory.{v₃, u₃} Scheme.{u}} [IsAlgebraicStack 𝒳]
  [IsAlgebraicStack 𝒴]

/-- **Corollary 4.6.9** (`cor:characterization-of-representable-morphisms`)
(Characterization of Representable Morphisms): let $F \colon \cX \to \cY$ be a morphism
of algebraic stacks whose relative diagonal $\cX \to \cX \times_{\cY} \cX$ is
representable by schemes. Then $F$ is representable (its base changes by schemes are
algebraic spaces) if and only if for every algebraically closed field $K$ and every point
$x \colon \Spec K \to \cX$, right-whiskering with $F$ is injective on the 2-automorphisms
of $x$ — equivalently, the homomorphism $G_x \to G_{F(x)}$ of stabilizer groups is
injective. (The book assumes $\cX$ and $\cY$ noetherian; noetherianness enters only
through the Existence of Minimal Presentations in the proof and is omitted from the
statement, noetherian stacks being part of the §4.3 ledger — see COMMENTARY.md.) -/
theorem representable_iff_injective_isoWhiskerRight (F : 𝒳 ⥤ᵇ 𝒴)
    (hdiag : F.diag.RelativelyRepresentable) :
    Representable F ↔
      ∀ (K : Type u) [Field K] [IsAlgClosed K]
        (x : overBased (Spec (CommRingCat.of K)) ⥤ᵇ 𝒳),
        Function.Injective
          (fun η : x ≅ x ↦ CategoryTheory.BasedCategory.isoWhiskerRight η F) := by
  sorry

end AlgebraicGeometry.BasedFunctor

end CorCharacterizationOfRepresentableMorphisms

section CorMgIsDm

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory in
/-- **Corollary 4.6.10** (`cor:mg-is-dm`): for `g ≥ 2` the moduli stack `ℳ_g` of smooth
curves of genus `g` is a Deligne–Mumford stack.

The intended proof (deferred) applies the Characterization of Deligne–Mumford Stacks
(Theorem 4.6.4): it suffices that the automorphism
group scheme `Aut(C)` of every smooth, connected, projective curve `C` over a field is
discrete and reduced, i.e. that its Lie algebra `T_{Aut(C),e} ≅ H⁰(C, T_C)` vanishes —
which holds because `deg T_C = 2 - 2g < 0` for `g ≥ 2`.

Blocked on first-order deformation theory
(Proposition C.2.4) and on the vanishing of
`H⁰(C, T_C)` for `g ≥ 2`, which needs the tangent sheaf `T_C` — the relative differentials
`Ω_{X/S}` are now available (`AlgebraicGeometry.Scheme.Hom.relativeDifferentials` in
`StacksAndModuli/API/RelativeDifferentials.lean`), but their dual, their local freeness on a smooth
curve, and degrees of line bundles on curves are not. -/
theorem isDeligneMumfordStack_moduliOfCurves (g : ℕ) (hg : 2 ≤ g) :
    IsDeligneMumfordStack (AlgebraicGeometry.Scheme.moduliOfCurves.{u} g) := by
  sorry

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory in
/-- **Corollary 4.6.10** (`cor:mg-is-dm`) (the finite-type clause): `ℳ_g` is of finite type
over `Spec ℤ` for `g ≥ 2`. -/
theorem finiteType_moduliOfCurves (g : ℕ) (hg : 2 ≤ g) :
    AlgebraicGeometry.BasedFunctor.FiniteType
      (AlgebraicGeometry.Scheme.moduliOfCurves.{u} g).toBase := by
  sorry

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory in
/-- Supporting consequence of Corollary 4.6.10: being of finite type over `Spec ℤ`,
`ℳ_g` is in particular locally of finite type. -/
theorem locallyOfFiniteType_moduliOfCurves (g : ℕ) (hg : 2 ≤ g) :
    AlgebraicGeometry.BasedFunctor.LocallyOfFiniteType
      (AlgebraicGeometry.Scheme.moduliOfCurves.{u} g).toBase :=
  (finiteType_moduliOfCurves g hg).1

end CorMgIsDm

section ExModuliAffineDiagonal

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ u

section CorMgIsDm

/-- **Corollary 4.6.10** (`cor:mg-is-dm`) (the affine-diagonal clause): the moduli stack
`ℳ_g` has affine diagonal, and is therefore quasi-separated.

Stated here rather than in §4.3 because `ℳ_g` is built in §4.1 part4.1.4 and the
diagonal-free form of "affine diagonal" is §4.5's `BasedCategory.HasAffineDiagonal` — for
all `Spec A → ℳ_g` and `Spec B → ℳ_g` the fibre product is affine. (See the §4.8
COMMENTARY on the two spellings of "affine diagonal": the diagonal-based
`BasedFunctor.HasAffineDiagonal` of Definition 4.3.11 is the same notion, but the
comparison is not formalized.)

The intended proof (deferred) is the quotient presentation `ℳ_g ≅ [H'/PGL_{5g-5}]` of
Theorem 4.1.17 together with Lemma 4.3.14: a quotient of a
scheme with affine diagonal by a smooth affine group scheme has affine diagonal. The
`Bun_{r,d}(C)` half of the example remains ledgered in §4.3 part4.3.3. -/
theorem hasAffineDiagonal_moduliOfCurves (g : ℕ) (hg : 2 ≤ g) :
    AlgebraicGeometry.BasedCategory.HasAffineDiagonal
      (AlgebraicGeometry.Scheme.moduliOfCurves.{u} g) := by
  sorry

end CorMgIsDm

end ExModuliAffineDiagonal
