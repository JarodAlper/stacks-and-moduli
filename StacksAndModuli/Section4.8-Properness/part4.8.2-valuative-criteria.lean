module

public import StacksAndModuli.«Section4.8-Properness».«part4.8.1-definitions»
public import StacksAndModuli.«Section4.1-Definitions».«part4.1.4-algebraicity-of-mg»
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Properness and the valuative criterion: the valuative criteria

This module formalizes `thm:valuative-criteria-stacks` and covers `exer:mg-is-separated`,
`exer:bun-satisfies-universally-closed-valuative-criterion`,
`exer:bun-is-not-universally-closed`, and `ex:base-changes-necessary-1`–`3` of §4.8
(Properness and the Valuative Criterion) of *Stacks and Moduli*,
label `sec:valuative-criteria`.

The main declarations are the four equivalences of `thm:valuative-criteria-stacks`
(proofs deferred to the
  ingredients listed in part 4.8.3), and recalls of Mathlib's scheme-level
  (valuation-ring-based) valuative criteria.

The examples and exercises on `BG`, `B𝔾ₘ`, `𝓜̄₁,₁`, `𝓜_g`, `Bun_{r,d}(C)`, `Bμₙ`, root
stacks, and `PGLₙ`-torsors are ledgered: they are blocked on classifying stacks, the
moduli stacks of curves and bundles, root stacks, and Brauer-group input.

**Exercise 4.8.12** (`exer:mg-is-separated`) is stated here — `ℳ_g` is separated over
`Spec ℤ` for `g ≥ 2` — now that `ℳ_g` exists (§4.1 part4.1.4); the proof is a recorded
obligation waiting on the valuative criterion above.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

section ThmValuativeCriteriaStacks

open CategoryTheory Functor AlgebraicGeometry CategoryTheory.BasedCategory
  AlgebraicGeometry.BasedCategory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- Background definition used in Theorem 4.8.7: a *valuative square* over
a morphism $f \colon \cX \to \cY$ of algebraic stacks is a 2-commutative diagram
$$\begin{matrix} \Spec K & \to & \cX \\ \downarrow & & \downarrow \\
\Spec R & \to & \cY \end{matrix}$$
where $R$ is a discrete valuation ring with fraction field $K$: morphisms of prestacks
$x \colon \Sch/\Spec K \to \cX$ and $y \colon \Sch/\Spec R \to \cY$ together with a
2-isomorphism $\alpha \colon f \circ x \cong y \circ j$, where $j \colon \Spec K \to
\Spec R$ is induced by $R \subseteq K$. For morphisms of schemes, Mathlib's
`AlgebraicGeometry.ValuativeCommSq` is the 1-categorical, valuation-ring-based analogue.
(DEPENDENCY, §4.7 parallel work: the fields `x`, `y`, `isoComm` form a 2-commutative
square `CategoryTheory.BasedFunctor.LiftingSq F S.specFractionMap` in the sense of
Remark 4.7.3, being formalized in
`Section4.7-Smoothness/part4.7.1-liftings.lean`; once §4.7 lands, this structure should
be refactored to bundle a `LiftingSq`.) -/
structure ValuativeCommSq (F : 𝒳 ⥤ᵇ 𝒴) where
  /-- The discrete valuation ring at the bottom left of the square. -/
  R : Type u
  /-- The ring structure of the discrete valuation ring. -/
  [commRing : CommRing R]
  /-- The discrete valuation ring is a domain. -/
  [isDomain : IsDomain R]
  /-- The discrete valuation ring structure. -/
  [isDiscreteValuationRing : IsDiscreteValuationRing R]
  /-- The fraction field at the top left of the square. -/
  K : Type u
  /-- The field structure of the fraction field. -/
  [field : Field K]
  /-- The algebra structure of the fraction field over the discrete valuation ring. -/
  [algebra : Algebra R K]
  /-- `K` is the fraction field of `R`. -/
  [isFractionRing : IsFractionRing R K]
  /-- The top morphism $\Spec K \to \cX$ of the square. -/
  x : overBased (Spec (CommRingCat.of K)) ⥤ᵇ 𝒳
  /-- The bottom morphism $\Spec R \to \cY$ of the square. -/
  y : overBased (Spec (CommRingCat.of R)) ⥤ᵇ 𝒴
  /-- The 2-isomorphism making the square 2-commutative. -/
  isoComm : x.comp F ≅
    (overBased.map (Spec.map (CommRingCat.ofHom (algebraMap R K)))).comp y

attribute [instance] ValuativeCommSq.commRing ValuativeCommSq.isDomain
  ValuativeCommSq.isDiscreteValuationRing ValuativeCommSq.field ValuativeCommSq.algebra
  ValuativeCommSq.isFractionRing

namespace ValuativeCommSq

variable {F : 𝒳 ⥤ᵇ 𝒴}

/-- The morphism $\Spec K \to \Spec R$ of schemes induced by the inclusion of the
discrete valuation ring of a valuative square into its fraction field. -/
noncomputable abbrev specFractionMap (S : ValuativeCommSq F) :
    Spec (CommRingCat.of S.K) ⟶ Spec (CommRingCat.of S.R) :=
  Spec.map (CommRingCat.ofHom (algebraMap S.R S.K))

/-- The field-valued point of $\cX$ given by the top morphism $\Spec K \to \cX$ of a
valuative square. -/
abbrev fieldPoint (S : ValuativeCommSq F) : FieldPoint 𝒳 :=
  { carrier := S.K, hom := S.x }

/- The following four whiskering lemmas and the `IsIso` instance duplicate
`CategoryTheory.BasedCategory.whiskerLeft_id`, `whiskerLeft_comp`, `whiskerRight_id`,
`whiskerRight_comp`, and `CategoryTheory.BasedFunctor.isIso_of_target_isFiberedInGroupoids`
introduced by the parallel formalization of Remark 4.7.3 in
`Section4.7-Smoothness/part4.7.1-liftings.lean` (§4.7), which cannot be imported while
§4.7 is in flight. They are placed in the `ValuativeCommSq` namespace to avoid name
clashes; once §4.7 lands, these copies should be removed in favor of the §4.7 originals. -/

/-- Left-whiskering of based natural transformations preserves identities. -/
lemma whiskerLeft_id {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒜 : BasedCategory.{v₄, u₄} 𝒮}
    {ℬ : BasedCategory.{v₅, u₅} 𝒮} {𝒞 : BasedCategory.{v₆, u₆} 𝒮} (G : 𝒜 ⥤ᵇ ℬ)
    (H : ℬ ⥤ᵇ 𝒞) :
    BasedCategory.whiskerLeft G (𝟙 H) = 𝟙 (G.comp H) := by
  apply BasedNatTrans.homCategory.ext
  rfl

/-- Left-whiskering of based natural transformations preserves composition. -/
lemma whiskerLeft_comp {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒜 : BasedCategory.{v₄, u₄} 𝒮}
    {ℬ : BasedCategory.{v₅, u₅} 𝒮} {𝒞 : BasedCategory.{v₆, u₆} 𝒮} (G : 𝒜 ⥤ᵇ ℬ)
    {H K L : ℬ ⥤ᵇ 𝒞} (α : H ⟶ K) (β : K ⟶ L) :
    BasedCategory.whiskerLeft G (α ≫ β) =
      BasedCategory.whiskerLeft G α ≫ BasedCategory.whiskerLeft G β := by
  apply BasedNatTrans.homCategory.ext
  rfl

/-- Right-whiskering of based natural transformations preserves identities. -/
lemma whiskerRight_id {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒜 : BasedCategory.{v₄, u₄} 𝒮}
    {ℬ : BasedCategory.{v₅, u₅} 𝒮} {𝒞 : BasedCategory.{v₆, u₆} 𝒮} (G : 𝒜 ⥤ᵇ ℬ)
    (H : ℬ ⥤ᵇ 𝒞) :
    BasedCategory.whiskerRight (𝟙 G) H = 𝟙 (G.comp H) := by
  apply BasedNatTrans.homCategory.ext
  ext a
  simp
  rfl

/-- Right-whiskering of based natural transformations preserves composition. -/
lemma whiskerRight_comp {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒜 : BasedCategory.{v₄, u₄} 𝒮}
    {ℬ : BasedCategory.{v₅, u₅} 𝒮} {𝒞 : BasedCategory.{v₆, u₆} 𝒮} {G H K : 𝒜 ⥤ᵇ ℬ}
    (α : G ⟶ H) (β : H ⟶ K) (L : ℬ ⥤ᵇ 𝒞) :
    BasedCategory.whiskerRight (α ≫ β) L =
      BasedCategory.whiskerRight α L ≫ BasedCategory.whiskerRight β L := by
  apply BasedNatTrans.homCategory.ext
  ext a
  simp

/-- Let `ℬ` be a prestack over `𝒮`. Every 2-morphism between morphisms of prestacks
`𝒜 → ℬ` is an isomorphism. (Universe-heterogeneous version of
`CategoryTheory.BasedNatTrans.isIso_of_isFiberedInGroupoids` of §3.4.3.) -/
instance isIso_of_target_isFiberedInGroupoids {𝒮 : Type u₁} [Category.{v₁} 𝒮]
    {𝒜 : BasedCategory.{v₄, u₄} 𝒮} {ℬ : BasedCategory.{v₅, u₅} 𝒮}
    [ℬ.p.IsFiberedInGroupoids] {G H : 𝒜 ⥤ᵇ ℬ} (α : G ⟶ H) : CategoryTheory.IsIso α := by
  have h : ∀ a : 𝒜.obj, CategoryTheory.IsIso (α.toNatTrans.app a) := fun a ↦
    Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id (p := ℬ.p)
      (S := 𝒜.p.obj a) (α.toNatTrans.app a)
  have : CategoryTheory.IsIso (X := G.toFunctor) (Y := H.toFunctor) α.toNatTrans :=
    NatIso.isIso_of_isIso_app α.toNatTrans
  exact BasedNatIso.isIso_of_toNatTrans_isIso α

/-- Background definition used in Theorem 4.8.7: let $S$ be a valuative square
over a morphism $f \colon \cX \to \cY$ of algebraic stacks, with 2-isomorphism
$\alpha \colon f \circ x \cong y \circ j$. A *lifting* of $S$ is a triple
$(\tilde{x}, \beta, \gamma)$ of a morphism $\tilde{x} \colon \Sch/\Spec R \to \cX$ and
2-isomorphisms $\beta \colon x \cong \tilde{x} \circ j$ and
$\gamma \colon f \circ \tilde{x} \cong y$ such that $\alpha$ is the composite of the
whiskerings $f(\beta)$ and $j^*\gamma$ (Remark 4.7.3). -/
structure Lifting (S : ValuativeCommSq F) where
  /-- The lifted morphism $\tilde{x} \colon \Spec R \to \cX$. -/
  lift : overBased (Spec (CommRingCat.of S.R)) ⥤ᵇ 𝒳
  /-- The 2-isomorphism $\beta \colon x \cong \tilde{x} \circ j$. -/
  isoX : S.x ≅ (overBased.map S.specFractionMap).comp lift
  /-- The 2-isomorphism $\gamma \colon f \circ \tilde{x} \cong y$. -/
  isoY : lift.comp F ≅ S.y
  /-- The triangle identity: the 2-isomorphism of the square is the composite of the
  whiskerings of `isoX` and `isoY`. -/
  w : S.isoComm.hom = BasedCategory.whiskerRight isoX.hom F ≫
    BasedCategory.whiskerLeft (overBased.map S.specFractionMap) isoY.hom

namespace Lifting

variable {S : ValuativeCommSq F}

/-- Background definition of morphisms of liftings used in Theorem 4.8.7: a morphism of
liftings $(\tilde{x}, \beta, \gamma) \to (\tilde{x}', \beta', \gamma')$ of a valuative square is
a 2-morphism $\Theta \colon \tilde{x} \to \tilde{x}'$ such that
$\beta' = j^*\Theta \circ \beta$ and $\gamma = \gamma' \circ f(\Theta)$. -/
@[ext]
structure Hom (L L' : S.Lifting) where
  /-- The underlying 2-morphism $\Theta \colon \tilde{x} \to \tilde{x}'$. -/
  hom : L.lift ⟶ L'.lift
  /-- Compatibility with the 2-isomorphisms $\beta$: $\beta' = j^*\Theta \circ \beta$. -/
  wX : L.isoX.hom ≫ BasedCategory.whiskerLeft (overBased.map S.specFractionMap) hom =
    L'.isoX.hom
  /-- Compatibility with the 2-isomorphisms $\gamma$:
  $\gamma = \gamma' \circ f(\Theta)$. -/
  wY : BasedCategory.whiskerRight hom F ≫ L'.isoY.hom = L.isoY.hom

/-- The identity morphism of a lifting of a valuative square. -/
@[simps]
noncomputable def Hom.id (L : S.Lifting) : Hom L L where
  hom := 𝟙 L.lift
  wX := by rw [whiskerLeft_id, Category.comp_id]
  wY := by rw [whiskerRight_id, Category.id_comp]

/-- The composition of morphisms of liftings of a valuative square. -/
@[simps]
noncomputable def Hom.comp {L L' L'' : S.Lifting} (φ : Hom L L') (ψ : Hom L' L'') :
    Hom L L'' where
  hom := φ.hom ≫ ψ.hom
  wX := by rw [whiskerLeft_comp, ← Category.assoc, φ.wX, ψ.wX]
  wY := by rw [whiskerRight_comp, Category.assoc, ψ.wY, φ.wY]

/-- The category of liftings of a valuative square. -/
noncomputable instance instCategory : Category S.Lifting where
  Hom := Hom
  id := Hom.id
  comp φ ψ := φ.comp ψ
  id_comp φ := by
    apply Hom.ext
    simp only [Hom.comp_hom, Hom.id_hom, Category.id_comp]
  comp_id φ := by
    apply Hom.ext
    simp only [Hom.comp_hom, Hom.id_hom, Category.comp_id]
  assoc φ ψ χ := by
    apply Hom.ext
    simp only [Hom.comp_hom, Category.assoc]

/-- The underlying 2-morphism of the identity morphism of a lifting. -/
@[simp]
lemma id_hom (L : S.Lifting) : Hom.hom (𝟙 L) = 𝟙 L.lift :=
  rfl

/-- The underlying 2-morphism of a composition of morphisms of liftings. -/
@[simp]
lemma comp_hom {L L' L'' : S.Lifting} (φ : L ⟶ L') (ψ : L' ⟶ L'') :
    Hom.hom (φ ≫ ψ) = φ.hom ≫ ψ.hom :=
  rfl

/-- The inverse of a morphism of liftings of a valuative square: since the target stack
is fibered in groupoids, the underlying 2-morphism is invertible, and its inverse is
compatible with the 2-isomorphisms of the liftings. -/
@[simps]
noncomputable def Hom.inv [𝒳.p.IsFiberedInGroupoids] {L L' : S.Lifting} (φ : L ⟶ L') :
    L' ⟶ L where
  hom := CategoryTheory.inv φ.hom
  wX := by
    rw [← φ.wX, Category.assoc, ← whiskerLeft_comp, IsIso.hom_inv_id, whiskerLeft_id,
      Category.comp_id]
  wY := by
    rw [← φ.wY, ← Category.assoc, ← whiskerRight_comp, IsIso.inv_hom_id, whiskerRight_id,
      Category.id_comp]

/-- Every morphism of liftings of a valuative square is an isomorphism. -/
instance [𝒳.p.IsFiberedInGroupoids] {L L' : S.Lifting} (φ : L ⟶ L') :
    CategoryTheory.IsIso φ :=
  ⟨Hom.inv φ, by apply Hom.ext; simp, by apply Hom.ext; simp⟩

/-- Supporting groupoid instance for Theorem 4.8.7: the liftings of a valuative square
over a morphism of algebraic stacks form a groupoid — every morphism of liftings is
invertible. The automorphism groups of this groupoid measure the ambiguity in part (4). -/
noncomputable instance [𝒳.p.IsFiberedInGroupoids] : Groupoid S.Lifting :=
  Groupoid.ofIsIso fun _ ↦ inferInstance

end Lifting

/-- Background definition of DVR extensions used in Theorem 4.8.7: an *extension of
discrete valuation rings* of a valuative square is a DVR $R'$ with fraction field $K'$,
an injective local
ring homomorphism $R \to R'$, and a compatible homomorphism $K \to K'$ of fraction
fields. (Faithfulness caveat: the book further requires $K \to K'$ to be of finite
transcendence degree; the criteria below are stated without this bound — both directions
remain true — and the bounded refinement is ledgered after
the theorem. See the `[decision]` entry in this folder's COMMENTARY.md.) -/
structure Extension (S : ValuativeCommSq F) where
  /-- The extension discrete valuation ring. -/
  R' : Type u
  /-- The ring structure of the extension. -/
  [commRing' : CommRing R']
  /-- The extension is a domain. -/
  [isDomain' : IsDomain R']
  /-- The discrete valuation ring structure of the extension. -/
  [isDiscreteValuationRing' : IsDiscreteValuationRing R']
  /-- The fraction field of the extension. -/
  K' : Type u
  /-- The field structure of the fraction field of the extension. -/
  [field' : Field K']
  /-- The algebra structure of the fraction field over the extension. -/
  [algebra' : Algebra R' K']
  /-- `K'` is the fraction field of `R'`. -/
  [isFractionRing' : IsFractionRing R' K']
  /-- The homomorphism $R \to R'$ of discrete valuation rings. -/
  ringHom : S.R →+* R'
  /-- The extension of discrete valuation rings is injective. -/
  injective : Function.Injective ringHom
  /-- The extension of discrete valuation rings is a local homomorphism. -/
  isLocalHom : IsLocalHom ringHom
  /-- The induced homomorphism $K \to K'$ of fraction fields. -/
  fieldHom : S.K →+* K'
  /-- The homomorphism of fraction fields is compatible with the extension. -/
  w : (algebraMap R' K').comp ringHom = fieldHom.comp (algebraMap S.R S.K)

attribute [instance] Extension.commRing' Extension.isDomain'
  Extension.isDiscreteValuationRing' Extension.field' Extension.algebra'
  Extension.isFractionRing' Extension.isLocalHom

namespace Extension

variable {S : ValuativeCommSq F} (E : S.Extension)

/-- The compatibility square of an extension of discrete valuation rings, at the level of
schemes: the two compositions $\Spec K' \to \Spec K \to \Spec R$ and
$\Spec K' \to \Spec R' \to \Spec R$ agree. -/
lemma specFractionMap_comp :
    Spec.map (CommRingCat.ofHom E.fieldHom) ≫ S.specFractionMap =
      Spec.map (CommRingCat.ofHom (algebraMap E.R' E.K')) ≫
        Spec.map (CommRingCat.ofHom E.ringHom) := by
  dsimp only [specFractionMap]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    E.w]

/-- The compatibility square of an extension of discrete valuation rings, at the level of
representable prestacks, composed with the bottom morphism of the valuative square. -/
lemma overBased_map_fieldHom_comp :
    (overBased.map (Spec.map (CommRingCat.ofHom E.fieldHom))).comp
        ((overBased.map S.specFractionMap).comp S.y) =
      (overBased.map (Spec.map (CommRingCat.ofHom (algebraMap E.R' E.K')))).comp
        ((overBased.map (Spec.map (CommRingCat.ofHom E.ringHom))).comp S.y) := by
  simp only [← BasedFunctor.comp_assoc, ← CategoryTheory.BasedCategory.overBased.map_comp,
    E.specFractionMap_comp]

/-- Supporting base-change construction for Theorem 4.8.7: the base change of a
valuative square along an extension of
discrete valuation rings — the square over the same morphism of stacks whose top
morphism is restricted along $\Spec K' \to \Spec K$ and whose bottom morphism is
restricted along $\Spec R' \to \Spec R$. -/
noncomputable def baseChange : ValuativeCommSq F where
  R := E.R'
  K := E.K'
  x := (overBased.map (Spec.map (CommRingCat.ofHom E.fieldHom))).comp S.x
  y := (overBased.map (Spec.map (CommRingCat.ofHom E.ringHom))).comp S.y
  isoComm :=
    whiskerLeftIso (overBased.map (Spec.map (CommRingCat.ofHom E.fieldHom))) S.isoComm ≪≫
      eqToIso E.overBased_map_fieldHom_comp

end Extension

end ValuativeCommSq

variable [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴]

/-- **Theorem 4.8.7** (`thm:valuative-criteria-stacks`) (part (1), Valuative Criterion
for Universal
Closedness): let $f \colon \cX \to \cY$ be a quasi-compact and quasi-separated morphism
of locally noetherian algebraic stacks. Then $f$ is universally closed if and only if
every valuative square over $f$ admits, after base change along some extension of
discrete valuation rings, a lifting. (Faithfulness caveat: the book produces extensions
whose fraction-field extension $K \to K'$ has finite transcendence degree; the criteria
are stated here without this bound, which is ledgered below — see COMMENTARY.md.) -/
theorem universallyClosed_iff_exists_extension_lifting
    (h𝒳 : BasedCategory.IsLocallyNoetherian 𝒳) (h𝒴 : BasedCategory.IsLocallyNoetherian 𝒴)
    {F : 𝒳 ⥤ᵇ 𝒴} (hqc : QuasiCompact F) (hqs : QuasiSeparated F) :
    UniversallyClosed F ↔
      ∀ S : ValuativeCommSq F, ∃ E : S.Extension, Nonempty E.baseChange.Lifting := by
  sorry

/-- **Theorem 4.8.7** (`thm:valuative-criteria-stacks`) (part (2), Valuative Criterion
for Properness): let
$f \colon \cX \to \cY$ be a quasi-compact and quasi-separated morphism of locally
noetherian algebraic stacks. Then $f$ is proper if and only if $f$ is of finite type and
every valuative square over $f$ admits, after base change along some extension of
discrete valuation rings, a lifting which is unique up to unique isomorphism. -/
theorem isProper_iff_finiteType_and_exists_extension_unique_lifting
    (h𝒳 : BasedCategory.IsLocallyNoetherian 𝒳) (h𝒴 : BasedCategory.IsLocallyNoetherian 𝒴)
    {F : 𝒳 ⥤ᵇ 𝒴} (hqc : QuasiCompact F) (hqs : QuasiSeparated F) :
    IsProper F ↔
      FiniteType F ∧ ∀ S : ValuativeCommSq F, ∃ E : S.Extension,
        Nonempty E.baseChange.Lifting ∧
          ∀ L₁ L₂ : E.baseChange.Lifting, Nonempty (Unique (L₁ ⟶ L₂)) := by
  sorry

/-- **Theorem 4.8.7** (`thm:valuative-criteria-stacks`) (part (3), Valuative Criterion
for Separatedness): let
$f \colon \cX \to \cY$ be a quasi-compact and quasi-separated morphism of locally
noetherian algebraic stacks. Then $f$ is separated if and only if any two liftings of a
valuative square over $f$ are uniquely isomorphic. -/
theorem isSeparated_iff_forall_lifting_nonempty_unique_hom
    (h𝒳 : BasedCategory.IsLocallyNoetherian 𝒳) (h𝒴 : BasedCategory.IsLocallyNoetherian 𝒴)
    {F : 𝒳 ⥤ᵇ 𝒴} (hqc : QuasiCompact F) (hqs : QuasiSeparated F) :
    IsSeparated F ↔
      ∀ (S : ValuativeCommSq F) (L₁ L₂ : S.Lifting), Nonempty (Unique (L₁ ⟶ L₂)) := by
  sorry

/-- **Theorem 4.8.7** (`thm:valuative-criteria-stacks`) (part (4), Valuative Criterion
for Separated
Diagonal): let $f \colon \cX \to \cY$ be a quasi-compact and quasi-separated morphism of
locally noetherian algebraic stacks. Then $f$ has separated diagonal if and only if
every automorphism of a lifting of a valuative square over $f$ is trivial. (The proof is
Exercise 4.8.23, part 4.8.3.) -/
theorem isSeparatedRepresentable_diag_iff_forall_lifting_hom_eq_id
    (h𝒳 : BasedCategory.IsLocallyNoetherian 𝒳) (h𝒴 : BasedCategory.IsLocallyNoetherian 𝒴)
    {F : 𝒳 ⥤ᵇ 𝒴} (hqc : QuasiCompact F) (hqs : QuasiSeparated F) :
    IsSeparatedRepresentable F.diag ↔
      ∀ (S : ValuativeCommSq F) (L : S.Lifting) (θ : L ⟶ L), θ = 𝟙 L := by
  sorry

/- Partial valuation-ring analogue of Theorem A.4.5, part (3): for morphisms of schemes,
Mathlib proves the valuation-ring-based valuative criteria; the book's DVR-based refinement
for noetherian schemes is listed as a "future project" in
`Mathlib/AlgebraicGeometry/ValuativeCriterion.lean`. A quasi-compact morphism of schemes
is universally closed if and only if it satisfies the existence part of the valuative
criterion. -/
example : @_root_.AlgebraicGeometry.UniversallyClosed.{u} =
    ValuativeCriterion.Existence ⊓ @_root_.AlgebraicGeometry.QuasiCompact :=
  _root_.AlgebraicGeometry.UniversallyClosed.eq_valuativeCriterion

/- Partial valuation-ring analogue of Theorem A.4.5, part (1): Mathlib's
valuation-ring analogue): a morphism of schemes is proper if and only if it is
quasi-compact, quasi-separated, locally of finite type, and satisfies the
(valuation-ring-based) valuative criterion. -/
example : @_root_.AlgebraicGeometry.IsProper.{u} =
    ValuativeCriterion ⊓ @_root_.AlgebraicGeometry.QuasiCompact ⊓
      @_root_.AlgebraicGeometry.QuasiSeparated ⊓
      @_root_.AlgebraicGeometry.LocallyOfFiniteType :=
  _root_.AlgebraicGeometry.IsProper.eq_valuativeCriterion

/- Partial valuation-ring analogue of Theorem A.4.5, part (2): Mathlib's
valuation-ring analogue): a quasi-separated morphism of schemes is separated if and only
if it satisfies the uniqueness part of the (valuation-ring-based) valuative
criterion. -/
example : @_root_.AlgebraicGeometry.IsSeparated.{u} =
    ValuativeCriterion.Uniqueness ⊓ @_root_.AlgebraicGeometry.QuasiSeparated :=
  _root_.AlgebraicGeometry.IsSeparated.eq_valuativeCriterion

/- LEDGER (`thm:valuative-criteria-stacks`, finite transcendence degree): the book's
statements (1) and (2) produce extensions of DVRs whose fraction-field extension
`K → K'` has finite transcendence degree. The strengthened criteria — the same
equivalences with `Extension` refined by a finite-transcendence-degree condition on
`fieldHom` — are deferred: the bound is produced by the proof of the universally closed
direction via `prop:geometry-dvrs` (appendix A.4, no StacksAndModuli section yet).

LEDGER (unlabeled good-practice exercise after `thm:valuative-criteria-stacks`): via the
valuative criterion, (a) `BG → Spec ℤ` is proper for an abstract finite group `G`;
(b) `B𝔾ₘ → Spec ℤ` is universally closed but not separated. Blocked on classifying
stacks `BG` (§3.4/§3.5 ledgers, `def:classifying-prestack`).

LEDGER (unlabeled hard exercise): the stack `𝓜̄₁,₁` of stable elliptic curves
(`exer:stack-of-elliptic-curves-is-algebraic`, §3.5/§4.1 ledgers) is proper over
`Spec ℤ`; the general statement for `𝓜̄_{g,n}` with `2g - 2 + n > 0` is
`thm:mg-is-proper` (§6.5). Blocked on the moduli stacks of curves. -/

end AlgebraicGeometry.BasedFunctor

end ThmValuativeCriteriaStacks

section ExerMgIsSeparated

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory in
/-- **Exercise 4.8.12** (`exer:mg-is-separated`): for `g ≥ 2` the moduli stack `ℳ_g` of
smooth curves of genus `g` is separated over `Spec ℤ`.

The intended proof (deferred) is part (3) of the valuative criterion: for a discrete valuation ring `R` with
fraction field `K`, two families of smooth curves over `Spec R` restricting to isomorphic
families over `Spec K` are isomorphic, and the isomorphism is unique — the special fibres
are smooth and proper, so an isomorphism over the generic point extends by properness and
is unique by separatedness of the fibres.

Blocked on the valuative criterion itself (still four recorded obligations) and, before
that, on the algebraicity of `ℳ_g` (Theorem 4.1.17). -/
theorem isSeparated_moduliOfCurves (g : ℕ) (hg : 2 ≤ g) :
    AlgebraicGeometry.BasedFunctor.IsSeparated
      (AlgebraicGeometry.Scheme.moduliOfCurves.{u} g).toBase := by
  sorry

/- LEDGER (unlabeled example: properness of `𝓜̄_{g,n}`): the moduli stack `𝓜̄_{g,n}` is
proper over `Spec ℤ` for `2g - 2 + n > 0`, i.e. excluding `(g, n) = (0,0), (0,1), (0,2),
(1,0)`; this is `thm:mg-is-proper`, proved in §6.5 (`sec:stable-reduction-proof`) in
characteristic `0` by verifying the valuative criterion. Blocked on the stack of *stable*
curves `𝓜̄_{g,n}` (Chapter 6) and on stable reduction (§6.5). -/

end ExerMgIsSeparated

section ExerBunSatisfiesUniversallyClosedValuativeCriterion

open AlgebraicGeometry

universe u

/- LEDGER (Exercise 4.8.14): for a smooth,
geometrically connected, projective curve `C` over a field `k`, the algebraic stacks
`Coh_{r,d}(C)` and `Bun_{r,d}(C)` satisfy the valuative criterion for universal
closedness, and no extension of DVRs is needed (via Proposition 2.4.2 on the properness
of Quot schemes). Blocked on the moduli stacks `Coh`/`Bun` and on Quot schemes (see the
§4.1 algebraicity ledger). -/

/- Background example for the unlabeled remark following Exercise 4.8.14: the
exercise does *not* imply that `Bun_{r,d}(C)` is universally closed — the valuative
criterion for universal closedness requires quasi-compactness, and `Bun_{r,d}(C)` is not
quasi-compact (as a later exercise on unboundedness explains). In fact a universally closed
morphism of schemes is necessarily quasi-compact (Stacks 04XU), recalled here from
Mathlib; presumably the same holds for morphisms of algebraic stacks. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyClosed f] : QuasiCompact f :=
  inferInstance

end ExerBunSatisfiesUniversallyClosedValuativeCriterion

section ExerBunIsNotUniversallyClosed

/- LEDGER (`exer:bun-is-not-universally-closed`): (a) `Bun_{r,d}(C)` is not universally
closed; (b) for an integral proper scheme `X` over a field of arbitrary dimension, the
stack `Coh^{tf}` of torsion free sheaves on `X` satisfies the valuative criterion for
universal closedness. Blocked on the moduli stacks `Bun`/`Coh` (§4.1 ledger). -/

end ExerBunIsNotUniversallyClosed

section ExBaseChangesNecessary1

/- "Are base changes necessary?" For the valuative criterion for properness of a
morphism of *schemes* it is not necessary to allow extensions of the DVR (this is
Mathlib's `AlgebraicGeometry.IsProper.eq_valuativeCriterion`, recalled above with
valuation rings); the same holds for finite type quasi-separated morphisms of algebraic
spaces (Stacks 0A40, not yet in Mathlib or StacksAndModuli). For general morphisms of algebraic
stacks extensions are necessary, as the following three examples show.

LEDGER (`ex:base-changes-necessary-1`): for the Deligne–Mumford stack `X = Bμₙ` over a
field `k` with characteristic prime to `n`, `R = k[x]_{(x)}` and `K = k(x)`, the
non-trivial `μₙ`-torsor `Spec K → Spec K`, `x ↦ xⁿ`, classifies a map `Spec K → Bμₙ`
that does not extend to `Spec R → Bμₙ` (all `μₙ`-torsors over `Spec R` are trivial), but
extends after the base change `K(x^{1/n})/K` to `Spec R[x^{1/n}] → Bμₙ`. Blocked on
classifying stacks and torsors (§3.4/§3.5/§4.1 ledgers, Stacks 06FI). -/

end ExBaseChangesNecessary1

section ExBaseChangesNecessary2

/- LEDGER (`ex:base-changes-necessary-2`): for `X = Spec R` the spectrum of a DVR with
uniformizer `π` and `𝒳` the `n`-th root stack `X(ⁿ√(𝒪_X/π))` (`ex:root-stacks`, §4.9
area), the morphism `𝒳 → X` is an isomorphism over the generic point, but the section
`Spec K → 𝒳` does not extend to a global section `X → 𝒳`. Blocked on root stacks. -/

end ExBaseChangesNecessary2

section ExBaseChangesNecessary3

/- If `G` is a special algebraic group over a field (every principal `G`-bundle is
Zariski-locally trivial), such as `SLₙ` or `GLₙ`, then `BG` satisfies the valuative
criterion for universal closedness without a base change: any map `Spec K → BG`
corresponds to the trivial principal `G`-bundle and extends to `Spec R → BG`. On the
other hand, base changes are necessary for `BPGLₙ`.

LEDGER (`ex:base-changes-necessary-3`): there is a principal `PGLₙ`-bundle over the
fraction field of a DVR that does not extend to the DVR (via a Brauer class in `Br(K)`
not in the image of `Br(R)`, cf. the Artin–Mumford example). Blocked on classifying
stacks and torsors (§3.4/§3.5/§4.1 ledgers) and on Brauer-group input, which is absent
from Mathlib. -/

end ExBaseChangesNecessary3
