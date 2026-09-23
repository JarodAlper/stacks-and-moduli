module

public import StacksAndModuli.API.ProjectiveCechH0CanonicalBaseChangeFromPushforward
public import StacksAndModuli.API.ProjectiveLineGradedCechH0TailRecurrence
public import StacksAndModuli.API.ProjectiveGradedCechAugmentationFlatness
public import StacksAndModuli.API.ProjectiveLineTwistedFreeQuotientCechVanishing

/-!
# Eventual flatness of a projective-line twisted-free quotient

For a twisted-free quotient on `ℙ¹` over an affine base, projective twisted
pushforwards in two adjacent degrees seed the two-variable Koszul recurrence.
Isomorphisms between their residue-field pullbacks and the corresponding
pushforwards on the fibres make the canonical Čech `H⁰` comparisons bijective
in those seed degrees.  First Čech cohomology vanishes throughout the tail, so
the recurrence propagates finite projectivity and base change.  Finally, the
bijective Čech augmentation transfers eventual flatness back to `Γ_*`.

Main declaration:

* `isFlatAbove_gammaStar_twistedFreeQuotient_of_pushforward_seed_baseChange`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory AlgebraicGeometry ProjectiveSpectrum.Twist

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Two finite-projective pushforward seeds and their residue-field
base-change isomorphisms make the intrinsic `Γ_*` of a twisted-free quotient
degreewise flat in every degree above the first seed. -/
theorem isFlatAbove_gammaStar_twistedFreeQuotient_of_pushforward_seed_baseChange
    (r : ℕ) (R : Type u) [CommRing R] (l : ℤ) (d q₀ q₁ : ℕ)
    (hd : l - 1 ≤ (d : ℤ))
    (Q : (Scheme.projectiveSpaceOver 1 (Spec (.of R))).Modules)
    [Q.IsQuasicoherent] [Q.IsFinitePresentation]
    (q : (∐ fun _ : ULift.{u} (Fin r) ↦
      Scheme.projectiveSpaceOverTwist 1 (Spec (.of R)) (-l)) ⟶ Q)
    [Epi q]
    (h₀ : Scheme.Modules.IsProjectiveOfRank q₀
      (Scheme.Modules.projectiveTwistedPushforward 1 Q d))
    (h₁ : Scheme.Modules.IsProjectiveOfRank q₁
      (Scheme.Modules.projectiveTwistedPushforward 1 Q (d + 1)))
    (e₀ : ∀ (I : Ideal R) [I.IsMaximal],
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R I.ResidueField)))).obj
          (Scheme.Modules.projectiveTwistedPushforward 1 Q d) ≅
        Scheme.Modules.projectiveTwistedPushforward 1
          (Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q
            (algebraMap R I.ResidueField)) d)
    (e₁ : ∀ (I : Ideal R) [I.IsMaximal],
      (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R I.ResidueField)))).obj
          (Scheme.Modules.projectiveTwistedPushforward 1 Q (d + 1)) ≅
        Scheme.Modules.projectiveTwistedPushforward 1
          (Scheme.Modules.projectiveSpaceBaseChangeOfRingHom Q
            (algebraMap R I.ResidueField)) (d + 1)) :
    GradedModule.IsFlatAbove
      (Proj.gammaStar
        (MvPolynomial.homogeneousSubmodule (Fin 2) R)
        (projSpecπ 1 R)
        ((Scheme.Modules.pullback
          (projectiveSpaceOverSpecIso 1 R).inv).obj Q)
        (stdVars 1 R)) (d : ℤ) := by
  let M := Proj.gammaStar
    (MvPolynomial.homogeneousSubmodule (Fin 2) R)
    (projSpecπ 1 R)
    ((Scheme.Modules.pullback
      (projectiveSpaceOverSpecIso 1 R).inv).obj Q)
    (stdVars 1 R)
  have hvan : ∀ t, Subsingleton
      ((M.cechHgr 1).obj (GradedModule.lineKoszulDegree (d : ℤ) t)) := by
    intro t
    apply subsingleton_cechHgr_one_gammaStar_twistedFreeQuotient
      r R l (GradedModule.lineKoszulDegree (d : ℤ) t) (by
        rw [GradedModule.lineKoszulDegree_eq_add]
        omega) Q q
  obtain ⟨hfin₀, hproj₀⟩ :=
    finite_projective_cechHgr_zero_gammaStar_of_projectiveTwistedPushforward_isProjectiveOfRank
      1 q₀ Q d h₀
  obtain ⟨hfin₁, hproj₁⟩ :=
    finite_projective_cechHgr_zero_gammaStar_of_projectiveTwistedPushforward_isProjectiveOfRank
      1 q₁ Q (d + 1) h₁
  have hβ₀ : ∀ (I : Ideal R) [I.IsMaximal], Function.Bijective
      (GradedModule.cechHgrZeroCanonicalBaseChangeHom
        (A := I.ResidueField) M (d : ℤ)) := by
    intro I hI
    letI hvan₀ : Subsingleton ((M.cechHgr 1).obj (d : ℤ)) := by
      simpa only [GradedModule.lineKoszulDegree_eq_add, Nat.cast_zero, add_zero]
        using hvan 0
    have hb :=
      cechHgrZeroCanonicalBaseChangeHom_bijective_of_projectiveTwistedPushforward_iso
        (algebraMap R I.ResidueField) Q q₀ d h₀ (e₀ I)
    have halg : (algebraMap R I.ResidueField).toAlgebra =
        (inferInstance : Algebra R I.ResidueField) :=
      Algebra.algebra_ext _ _ (fun x ↦ rfl)
    rw [halg] at hb
    simpa only [M] using hb
  have hβ₁ : ∀ (I : Ideal R) [I.IsMaximal], Function.Bijective
      (GradedModule.cechHgrZeroCanonicalBaseChangeHom
        (A := I.ResidueField) M ((d : ℤ) + 1)) := by
    intro I hI
    letI hvan₁ : Subsingleton ((M.cechHgr 1).obj ((d : ℤ) + 1)) := by
      simpa only [GradedModule.lineKoszulDegree_eq_add, Nat.cast_one]
        using hvan 1
    haveI hvan₁' : Subsingleton ((M.cechHgr 1).obj ((d + 1 : ℕ) : ℤ)) := by
      rw [show ((d + 1 : ℕ) : ℤ) = (d : ℤ) + 1 by omega]
      infer_instance
    have hb :=
      cechHgrZeroCanonicalBaseChangeHom_bijective_of_projectiveTwistedPushforward_iso
        (algebraMap R I.ResidueField) Q q₁ (d + 1) h₁ (e₁ I)
    have halg : (algebraMap R I.ResidueField).toAlgebra =
        (inferInstance : Algebra R I.ResidueField) :=
      Algebra.algebra_ext _ _ (fun x ↦ rfl)
    rw [halg] at hb
    rw [show ((d + 1 : ℕ) : ℤ) = (d : ℤ) + 1 by omega] at hb
    simpa only [M] using hb
  have hrec :=
    GradedModule.finite_projective_and_canonicalBaseChange_cechHgr_zero_tail
      M (d : ℤ) hvan hfin₀ hproj₀ hfin₁ hproj₁ hβ₀ hβ₁
  have hH₀ : GradedModule.IsFlatAbove (M.cechHgr 0) (d : ℤ) := by
    intro z hz
    let t := (z - (d : ℤ)).toNat
    have htz : GradedModule.lineKoszulDegree (d : ℤ) t = z := by
      rw [GradedModule.lineKoszulDegree_eq_add]
      dsimp only [t]
      rw [Int.toNat_of_nonneg (sub_nonneg.mpr hz)]
      omega
    have hproj := (hrec t).1.2
    rw [← htz]
    letI := hproj
    exact Module.Flat.of_projective
  apply GradedModule.isFlatAbove_of_cechAug_bijective M (d : ℤ) hH₀
  intro z _
  exact bijective_gammaStar_cechAug_of_isFinitePresentation
    (projSpecπ 1 R)
    ((Scheme.Modules.pullback
      (projectiveSpaceOverSpecIso 1 R).inv).obj Q) z

end AlgebraicGeometry.ProjectiveSpace

end

end
