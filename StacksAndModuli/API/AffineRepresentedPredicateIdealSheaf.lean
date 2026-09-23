module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Ideal sheaves from affine-represented predicates

Suppose that, on every affine open `U` of a scheme, a predicate on ring maps out of
`Γ(U, 𝒪_U)` is represented by an ideal `J(U)`.  If the predicates agree after passing
from `U` to a principal open, then the ideals automatically localize.  Indeed, each of
the two required inclusions is tested against the quotient by one of the two ideals.

This file packages that argument as an `IdealSheafData` constructor.  It is useful when
local equations arise from noncanonical finite presentations: compatibility of the
equations themselves need not be chosen, because compatibility follows from their common
universal property.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- Affine ideals representing a predicate which is compatible with restriction to
principal opens.

The predicate is deliberately ring-theoretic.  In geometric applications,
`condition U A f` says that the morphism `Spec A ⟶ U ⟶ X` obtained from `f`
has a specified pullback-stable property. -/
structure AffineRepresentedPredicate where
  /-- The predicate on maps from the coordinate ring of an affine open. -/
  condition : (U : X.affineOpens) → (A : Type u) → [CommRing A] →
    (Γ(X, U.1) →+* A) → Prop
  /-- The ideal representing the predicate on each affine open. -/
  ideal : (U : X.affineOpens) → Ideal Γ(X, U.1)
  /-- The affine universal property. -/
  represents : ∀ (U : X.affineOpens) (A : Type u) [CommRing A]
    (f : Γ(X, U.1) →+* A),
      condition U A f ↔ ideal U ≤ RingHom.ker f
  /-- The predicate is unchanged when the same morphism is expressed through a
  principal affine open. -/
  basicOpen_iff : ∀ (U : X.affineOpens) (r : Γ(X, U.1))
    (A : Type u) [CommRing A]
    (f : Γ(X, X.affineBasicOpen r) →+* A),
      condition (X.affineBasicOpen r) A f ↔
        condition U A
          (f.comp (X.presheaf.map
            (homOfLE (X.basicOpen_le r)).op).hom)

namespace AffineRepresentedPredicate

variable {X}

/-- Ideals representing a common affine-local predicate commute with restriction to a
principal open. -/
lemma map_ideal_basicOpen (D : AffineRepresentedPredicate X)
    (U : X.affineOpens) (r : Γ(X, U.1)) :
    (D.ideal U).map
        (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom =
      D.ideal (X.affineBasicOpen r) := by
  let V := X.affineBasicOpen r
  let ρ : Γ(X, U.1) →+* Γ(X, V) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  apply le_antisymm
  · let q : Γ(X, V) →+* Γ(X, V) ⧸ D.ideal V :=
      Ideal.Quotient.mk (D.ideal V)
    have hV : D.condition V (Γ(X, V) ⧸ D.ideal V) q :=
      (D.represents V _ q).mpr (by rw [Ideal.mk_ker])
    have hU : D.condition U (Γ(X, V) ⧸ D.ideal V) (q.comp ρ) :=
      (D.basicOpen_iff U r _ q).mp hV
    have hker : D.ideal U ≤ RingHom.ker (q.comp ρ) :=
      (D.represents U _ (q.comp ρ)).mp hU
    rw [← RingHom.comap_ker] at hker
    exact (Ideal.map_le_iff_le_comap.mpr hker).trans_eq Ideal.mk_ker
  · let J : Ideal Γ(X, V) := (D.ideal U).map ρ
    let q : Γ(X, V) →+* Γ(X, V) ⧸ J := Ideal.Quotient.mk J
    have hker : D.ideal U ≤ RingHom.ker (q.comp ρ) := by
      rw [← RingHom.comap_ker, Ideal.mk_ker]
      exact Ideal.le_comap_map
    have hU : D.condition U (Γ(X, V) ⧸ J) (q.comp ρ) :=
      (D.represents U _ (q.comp ρ)).mpr hker
    have hV : D.condition V (Γ(X, V) ⧸ J) q :=
      (D.basicOpen_iff U r _ q).mpr hU
    have : D.ideal V ≤ RingHom.ker q :=
      (D.represents V _ q).mp hV
    rw [Ideal.mk_ker] at this
    change D.ideal V ≤ J
    exact this

/-- The ideal sheaf represented by a compatible family of affine predicates. -/
noncomputable def toIdealSheafData (D : AffineRepresentedPredicate X) :
    X.IdealSheafData where
  ideal := D.ideal
  map_ideal_basicOpen := D.map_ideal_basicOpen

@[simp]
lemma toIdealSheafData_ideal (D : AffineRepresentedPredicate X)
    (U : X.affineOpens) :
    D.toIdealSheafData.ideal U = D.ideal U :=
  rfl

end AffineRepresentedPredicate

/-- Expressing an affine morphism through a principal affine open or through the
ambient affine open gives the same morphism to the scheme. -/
lemma specMap_comp_affineBasicOpen_isoSpec_inv_ι
    (U : X.affineOpens) (r : Γ(X, U.1))
    (A : Type u) [CommRing A]
    (f : Γ(X, X.affineBasicOpen r) →+* A) :
    Spec.map (CommRingCat.ofHom f) ≫
          (X.affineBasicOpen r).2.isoSpec.inv ≫
          (X.affineBasicOpen r).1.ι =
      Spec.map (CommRingCat.ofHom
          (f.comp (X.presheaf.map
            (homOfLE (X.basicOpen_le r)).op).hom)) ≫
        U.2.isoSpec.inv ≫ U.1.ι := by
  let ρ := (X.presheaf.map (homOfLE (X.basicOpen_le r)).op)
  have hinner :
      (X.affineBasicOpen r).2.isoSpec.inv ≫
          (X.affineBasicOpen r).1.ι =
        Spec.map ρ ≫ U.2.isoSpec.inv ≫ U.1.ι := by
    simpa only [ρ, IsAffineOpen.fromSpec] using
      (U.2.map_fromSpec (X.affineBasicOpen r).2
        (homOfLE (X.basicOpen_le r)).op).symm
  rw [hinner]
  simp only [← Category.assoc, ← Spec.map_comp, CommRingCat.ofHom_comp]
  simp only [ρ, CommRingCat.ofHom_hom]

/-- Affine ideals representing a geometric predicate on morphisms into a scheme.

Compared with `AffineRepresentedPredicate`, the compatibility on principal opens is
automatic: both ring maps define literally the same morphism into `X`. -/
structure AffineMorphismPredicate where
  /-- The geometric predicate on morphisms from affine schemes. -/
  condition : (W : Scheme.{u}) → [IsAffine W] → (W ⟶ X) → Prop
  /-- Its representing ideal on each affine open. -/
  ideal : (U : X.affineOpens) → Ideal Γ(X, U.1)
  /-- The affine universal property. -/
  represents : ∀ (U : X.affineOpens) (A : Type u) [CommRing A]
    (f : Γ(X, U.1) →+* A),
      condition (Spec (.of A))
          (Spec.map (CommRingCat.ofHom f) ≫ U.2.isoSpec.inv ≫ U.1.ι) ↔
        ideal U ≤ RingHom.ker f

namespace AffineMorphismPredicate

variable {X}

/-- Forget the geometric presentation of the predicate and retain its compatible
ring-level affine universal properties. -/
noncomputable def toAffineRepresentedPredicate
    (D : AffineMorphismPredicate X) : AffineRepresentedPredicate X where
  condition U A _ f :=
    D.condition (Spec (.of A))
      (Spec.map (CommRingCat.ofHom f) ≫ U.2.isoSpec.inv ≫ U.1.ι)
  ideal := D.ideal
  represents := D.represents
  basicOpen_iff U r A _ f := by
    rw [specMap_comp_affineBasicOpen_isoSpec_inv_ι X U r A f]

/-- The ideal sheaf canonically determined by affine closed equations for a geometric
predicate. -/
noncomputable def toIdealSheafData (D : AffineMorphismPredicate X) :
    X.IdealSheafData :=
  D.toAffineRepresentedPredicate.toIdealSheafData

@[simp]
lemma toIdealSheafData_ideal (D : AffineMorphismPredicate X)
    (U : X.affineOpens) :
    D.toIdealSheafData.ideal U = D.ideal U :=
  rfl

/-- The affine closed chart represents the predicate on an arbitrary affine source,
provided the predicate is invariant under precomposition by isomorphisms. -/
lemma condition_iff_exists_affineChartLift
    (D : AffineMorphismPredicate X)
    (hiso : ∀ (W W' : Scheme.{u}) [IsAffine W] [IsAffine W']
      (e : W ≅ W') (g : W' ⟶ X),
        D.condition W (e.hom ≫ g) ↔ D.condition W' g)
    (U : X.affineOpens) (W : Scheme.{u}) [IsAffine W]
    (ψ : W ⟶ U.1.toScheme) :
    D.condition W (ψ ≫ U.1.ι) ↔
      ∃ h : W ⟶ D.toIdealSheafData.glueDataObj U,
        h ≫ D.toIdealSheafData.glueDataObjι U = ψ := by
  let eW := W.isoSpec
  let c : Spec Γ(W, ⊤) ⟶ Spec Γ(X, U.1) :=
    eW.inv ≫ ψ ≫ U.2.isoSpec.hom
  let f : Γ(X, U.1) →+* Γ(W, ⊤) := (Spec.preimage c).hom
  have hmap : Spec.map (CommRingCat.ofHom f) = c := by
    simpa only [f, CommRingCat.ofHom_hom] using Spec.map_preimage c
  have hcanonical :
      Spec.map (CommRingCat.ofHom f) ≫ U.2.isoSpec.inv ≫ U.1.ι =
        eW.inv ≫ ψ ≫ U.1.ι := by
    rw [hmap]
    simp [c]
  have hcondition :
      D.condition W (ψ ≫ U.1.ι) ↔
        D.condition (Spec Γ(W, ⊤))
          (Spec.map (CommRingCat.ofHom f) ≫ U.2.isoSpec.inv ≫ U.1.ι) := by
    rw [hcanonical]
    exact (hiso (Spec Γ(W, ⊤)) W eW.symm (ψ ≫ U.1.ι)).symm
  rw [hcondition]
  refine (D.represents U Γ(W, ⊤) f).trans ?_
  constructor
  · intro hf
    let q : (Γ(X, U.1) ⧸ D.ideal U) →+* Γ(W, ⊤) :=
      Ideal.Quotient.lift (D.ideal U) f
        (fun _x hx ↦ RingHom.mem_ker.mp (hf hx))
    let h₀ : Spec Γ(W, ⊤) ⟶ D.toIdealSheafData.glueDataObj U :=
      Spec.map (CommRingCat.ofHom q)
    refine ⟨eW.hom ≫ h₀, ?_⟩
    rw [← cancel_epi eW.inv]
    simp only [Iso.inv_hom_id_assoc, Category.assoc]
    change h₀ ≫
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (D.ideal U))) ≫
          U.2.isoSpec.inv) = eW.inv ≫ ψ
    rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
        (q.comp (Ideal.Quotient.mk (D.ideal U)))) ≫ U.2.isoSpec.inv = _
    rw [show q.comp (Ideal.Quotient.mk (D.ideal U)) = f from rfl,
      hmap]
    simp [c]
  · rintro ⟨h, hh⟩
    intro x hx
    rw [RingHom.mem_ker]
    let h₀ : Spec Γ(W, ⊤) ⟶ D.toIdealSheafData.glueDataObj U :=
      eW.inv ≫ h
    have hh₀ : h₀ ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (D.ideal U))) =
          Spec.map (CommRingCat.ofHom f) := by
      rw [← cancel_mono U.2.isoSpec.inv]
      change h₀ ≫
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (D.ideal U))) ≫
            U.2.isoSpec.inv) =
        Spec.map (CommRingCat.ofHom f) ≫ U.2.isoSpec.inv
      change (eW.inv ≫ h) ≫ D.toIdealSheafData.glueDataObjι U = _
      rw [Category.assoc, hh, hmap]
      simp [c]
    have hring :
        (Spec.preimage h₀).hom.comp (Ideal.Quotient.mk (D.ideal U)) = f := by
      have hcat :
          CommRingCat.ofHom (Ideal.Quotient.mk (D.ideal U)) ≫
              Spec.preimage h₀ = CommRingCat.ofHom f := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage]
        exact hh₀
      exact congrArg CommRingCat.Hom.hom hcat
    rw [← DFunLike.congr_fun hring x]
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]

end AffineMorphismPredicate

end AlgebraicGeometry.Scheme
