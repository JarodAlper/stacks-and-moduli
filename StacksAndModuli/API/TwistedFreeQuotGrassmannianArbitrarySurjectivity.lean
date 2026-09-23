module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianResidueSurjectivity

/-!
# Arbitrary-base surjectivity for the Quot-to-Grassmannian map

This file removes the locally noetherian hypothesis from the uniform projective-space
regularity theorem once the fixed-degree target is known to be finite locally free and
its canonical base-change map is invertible.  Surjectivity is checked after the residue
field of every maximal ideal on every affine open, where the existing locally noetherian
theorem applies, and is then descended by affine Nakayama.

Main declaration:
- `AlgebraicGeometry.ProjectiveSpace.exists_bound_surjective_twistedFreeQuotGrassmannianFreeMap_arbitrary_of_rank_and_baseChange`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpace

open _root_.AlgebraicGeometry.ProjectiveSpace

/-- The locally noetherian uniform generation bound works over every base once the
fixed-degree pushforward is a vector bundle and the canonical pushforward base-change
morphism is invertible.  These are precisely the two remaining fixed-degree conclusions
of Cohomology and Base Change. -/
theorem
    exists_bound_surjective_twistedFreeQuotGrassmannianFreeMap_arbitrary_of_rank_and_baseChange
    (n r : ℕ) (l : ℤ) (P : Polynomial ℚ) :
    ∃ d₁ : ℤ, 0 ≤ d₁ ∧ ∀ (S : Scheme.{u}) (T : Over S)
      (a : Scheme.Modules.QuotientPullbackData
        (Scheme.Modules.QuotientPullbackData.twistedFreeAmbient
          (n := n) (r := r) (l := l))
        (Scheme.projectiveSpaceOverπ n S) T),
      a.HasFiberwiseHilbertPolynomial P →
      ∀ (d e : ℕ) (he : (d : ℤ) - l = (e : ℤ)), d₁ ≤ (d : ℤ) →
      ∀ {m q : ℕ}
        (σ : ULift.{u} (Fin m) ≃ ULift.{u} (Fin r) × Fin ((n + e).choose n)),
      Scheme.Modules.IsProjectiveOfRank q
          (Scheme.twistedFreeQuotientTwistPushforward n S l r a d) →
      Scheme.TwistedFreeQuotGrassmannianCanonicalBaseChangeData
          n S l r P d e he m σ →
      ∀ U : T.left.affineOpens,
      Function.Surjective (Scheme.Modules.finFreeSectionsMap'
        (Scheme.twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) U.1) := by
  obtain ⟨d₁, hd₁0, hlocal⟩ :=
    AlgebraicGeometry.Scheme.ProjectiveSpace.exists_bound_surjective_twistedFreeQuotGrassmannianFreeMap.{u}
      n r l P
  refine ⟨d₁, hd₁0, ?_⟩
  intro S T a hP d e he hd m q σ hM B U
  let p := Scheme.twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ
  letI : (Scheme.twistedFreeQuotientTwistPushforward n S l r a d).IsQuasicoherent :=
    Scheme.twistedFreeQuotientTwistPushforward_isQuasicoherent n S l r a d
  apply Scheme.Modules.finFreeSectionsMap'_surjective_of_geometric_residue_pullbacks_of_rank
    p hM U
  intro I hI
  letI : Field (Γ(T.left, U.1) ⧸ I) := @Ideal.Quotient.field _ _ I hI
  let i := U.1.ι
  let j := U.2.isoSpec.inv
  let k := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let f := k ≫ (j ≫ i)
  let Tκ : Over S := Over.mk (f ≫ T.hom)
  let g : Tκ ⟶ T := Over.homMk f rfl
  let aκ := a.pullback g
  let pκ := Scheme.twistedFreeQuotGrassmannianFreeMap n S l r aκ d e he σ
  let β := Scheme.twistedFreeQuotientTwistPushforwardBaseChangeHom n S l r g a d
  let freeIso := Scheme.Modules.pullbackFreeIso f (ULift.{u} (Fin m))
  letI : IsAffine Tκ.left := by
    change IsAffine (Spec (.of (Γ(T.left, U.1) ⧸ I)))
    infer_instance
  letI : IsLocallyNoetherian Tκ.left := by
    change IsLocallyNoetherian (Spec (.of (Γ(T.left, U.1) ⧸ I)))
    infer_instance
  letI : IsIso β := B.baseChange_isIso g a hP
  have hPκ : aκ.HasFiberwiseHilbertPolynomial P :=
    a.hasFiberwiseHilbertPolynomial_pullback g hP
  have hpκ' : ∀ V : Tκ.left.affineOpens, Function.Surjective
      (Scheme.Modules.finFreeSectionsMap' pκ V.1) :=
    hlocal S Tκ aκ hPκ d e he hd σ
  have hpκ : Function.Surjective (Scheme.Modules.Hom.app pκ ⊤) := by
    let V : Tκ.left.affineOpens := ⟨⊤, isAffineOpen_top Tκ.left⟩
    exact Scheme.Modules.hom_app_surjective_of_finFreeSectionsMap'_surjective
      pκ hpκ' V
  have hsq :
      (Scheme.Modules.pullback f).map p ≫ (asIso β).hom =
        freeIso.hom ≫ pκ := by
    rw [← cancel_epi freeIso.inv]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, asIso_hom]
    change (Scheme.Modules.pullbackFreeIso g.left (ULift.{u} (Fin m))).inv ≫
        (Scheme.Modules.pullback g.left).map
          (Scheme.twistedFreeQuotGrassmannianFreeMap n S l r a d e he σ) ≫
        Scheme.twistedFreeQuotientTwistPushforwardBaseChangeHom n S l r g a d =
      Scheme.twistedFreeQuotGrassmannianFreeMap n S l r (a.pullback g) d e he σ
    exact B.freeMap_baseChange g a
  exact Scheme.Modules.surjective_app_of_arrow_iso
    ((Scheme.Modules.pullback f).map p) pκ freeIso (asIso β) hsq ⊤ hpκ

end AlgebraicGeometry.ProjectiveSpace

end

end
