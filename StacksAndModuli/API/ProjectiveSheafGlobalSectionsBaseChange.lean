module

public import StacksAndModuli.API.FiniteProjectiveFiberRank
public import StacksAndModuli.API.DVRHilbertPolynomial

/-!
# Eventual base change for global sections on projective space

For a coherent sheaf `Q` on projective space over a noetherian affine base, relative
Serre vanishing and Cohomology and Base Change imply that `H⁰(Q(d))` is finite projective
and commutes with arbitrary base change for all sufficiently large `d`.  This file packages
that precise scheme-level output and proves the resulting constancy of Hilbert polynomials
over a local base.

The package is deliberately stated using actual tensor-product comparison equivalences.
Thus constructing it from a finitely presented flat sheaf is exactly the remaining
geometric input; all subsequent finite-projective rank and Hilbert-polynomial arguments
are proved here.

Main declarations:

* `Scheme.Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange`;
* `HasEventualFiniteProjectiveGlobalSectionsBaseChange.hasHilbertPolynomialOver_baseChange_iff`;
* `HasEventualFiniteProjectiveGlobalSectionsBaseChange.hasFiberwiseHilbertPolynomial_of_baseChange`;
* `hasFiberwiseHilbertPolynomial_of_baseChange_iso`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory TopologicalSpace Opposite TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- Base change of a sheaf on relative projective space along a homomorphism of affine
base rings. -/
noncomputable def Modules.projectiveSpaceBaseChangeOfRingHom
    {n : ℕ} {R K : Type u} [CommRing R] [CommRing K]
    (Q : (projectiveSpaceOver n (Spec (.of R))).Modules) (f : R →+* K) :
    (projectiveSpaceOver n (Spec (.of K))).Modules :=
  (Modules.pullback
    (projectiveSpaceOverMap n (Spec.map (CommRingCat.ofHom f)))).obj Q

/-- The underlying type of the global sections of `Q(d)` on relative projective space.
Its base-ring module structure is installed locally using
`Scheme.Modules.globalSectionsModule`. -/
abbrev Modules.projectiveSpaceTwistedGlobalSections
    {n : ℕ} {R : Type u} [CommRing R]
    (Q : (projectiveSpaceOver n (Spec (.of R))).Modules) (d : ℤ) : Type u :=
  Γ(projectiveSpaceOverTwistModule Q d, ⊤)

/-- The eventual conclusion of relative Serre vanishing and Cohomology and Base Change
for a sheaf on projective space over an affine base.

For every sufficiently large twist, global sections form a finite projective module on
the base and their formation commutes with every field extension of the coefficient
ring.  The comparison is recorded as a genuine linear equivalence
`K ⊗_R H⁰(Q(d)) ≃ H⁰(Q_K(d))`. -/
structure Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange
    {n : ℕ} {R : Type u} [CommRing R]
    (Q : (projectiveSpaceOver n (Spec (.of R))).Modules) : Type (u + 1) where
  /-- A twist from which finite projectivity and base change hold. -/
  bound : ℕ
  /-- Eventual finiteness of global sections over the base. -/
  finite : ∀ (d : ℕ), bound ≤ d →
    letI := Modules.globalSectionsModule (projectiveSpaceOverπ n (Spec (.of R)))
      (projectiveSpaceOverTwistModule Q (d : ℤ))
    Module.Finite R (Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ))
  /-- Eventual projectivity of global sections over the base. -/
  projective : ∀ (d : ℕ), bound ≤ d →
    letI := Modules.globalSectionsModule (projectiveSpaceOverπ n (Spec (.of R)))
      (projectiveSpaceOverTwistModule Q (d : ℤ))
    Module.Projective R (Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ))
  /-- Eventual formation of global sections commutes with field extension. -/
  baseChangeIso : ∀ (K : Type u) [Field K] (f : R →+* K)
      (d : ℕ), bound ≤ d →
    letI : Algebra R K := f.toAlgebra
    letI := Modules.globalSectionsModule (projectiveSpaceOverπ n (Spec (.of R)))
      (projectiveSpaceOverTwistModule Q (d : ℤ))
    let QK := Modules.projectiveSpaceBaseChangeOfRingHom Q f
    letI := Modules.globalSectionsModule (projectiveSpaceOverπ n (Spec (.of K)))
      (projectiveSpaceOverTwistModule QK (d : ℤ))
    K ⊗[R] Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ) ≃ₗ[K]
      Modules.projectiveSpaceTwistedGlobalSections QK (d : ℤ)

namespace Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange

variable {n : ℕ} {R : Type u} [CommRing R]
variable {Q : (projectiveSpaceOver n (Spec (.of R))).Modules}

/-- In a sufficiently large twist, the dimension on a field base change is the rank of
the finite projective module of relative global sections. -/
theorem hilbertFunctionOver_baseChange_eq [IsLocalRing R]
    (H : Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange Q)
    (K : Type u) [Field K] (f : R →+* K) (d : ℕ) (hd : H.bound ≤ d) :
    hilbertFunctionOver (Modules.projectiveSpaceBaseChangeOfRingHom Q f) (d : ℤ) =
      letI := Modules.globalSectionsModule (projectiveSpaceOverπ n (Spec (.of R)))
        (projectiveSpaceOverTwistModule Q (d : ℤ))
      Module.finrank R (Modules.projectiveSpaceTwistedGlobalSections Q (d : ℤ)) := by
  letI : Algebra R K := f.toAlgebra
  let Qd := projectiveSpaceOverTwistModule Q (d : ℤ)
  let QK := Modules.projectiveSpaceBaseChangeOfRingHom Q f
  let QKd := projectiveSpaceOverTwistModule QK (d : ℤ)
  letI : Module R Γ(Qd, ⊤) :=
    Modules.globalSectionsModule (projectiveSpaceOverπ n (Spec (.of R))) Qd
  letI : Module K Γ(QKd, ⊤) :=
    Modules.globalSectionsModule (projectiveSpaceOverπ n (Spec (.of K))) QKd
  letI : Module.Finite R Γ(Qd, ⊤) := H.finite d hd
  letI : Module.Projective R Γ(Qd, ⊤) := H.projective d hd
  change Module.finrank K Γ(QKd, ⊤) = Module.finrank R Γ(Qd, ⊤)
  rw [← (H.baseChangeIso K f d hd).finrank_eq]
  exact Module.finrank_tensorProduct_eq_of_finite_projective_of_isLocalRing

/-- Any two field base changes of a projective-space sheaf satisfying eventual `H⁰`
base change have equal Hilbert functions in all sufficiently large degrees. -/
theorem eventually_hilbertFunctionOver_baseChange_eq [IsLocalRing R]
    (H : Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange Q)
    (K L : Type u) [Field K] [Field L] (f : R →+* K) (g : R →+* L) :
    ∀ᶠ d : ℕ in Filter.atTop,
      hilbertFunctionOver (Modules.projectiveSpaceBaseChangeOfRingHom Q f) (d : ℤ) =
        hilbertFunctionOver (Modules.projectiveSpaceBaseChangeOfRingHom Q g) (d : ℤ) := by
  filter_upwards [Filter.eventually_ge_atTop H.bound] with d hd
  rw [H.hilbertFunctionOver_baseChange_eq K f d hd,
    H.hilbertFunctionOver_baseChange_eq L g d hd]

/-- Hilbert polynomial is invariant between any two field base changes once eventual
finite-projective `H⁰` and base change are available. -/
theorem hasHilbertPolynomialOver_baseChange_iff [IsLocalRing R]
    (H : Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange Q)
    (K L : Type u) [Field K] [Field L] (f : R →+* K) (g : R →+* L)
    (P : Polynomial ℚ) :
    HasHilbertPolynomialOver (Modules.projectiveSpaceBaseChangeOfRingHom Q f) P ↔
      HasHilbertPolynomialOver (Modules.projectiveSpaceBaseChangeOfRingHom Q g) P := by
  have heq := H.eventually_hilbertFunctionOver_baseChange_eq K L f g
  constructor
  · intro h
    filter_upwards [h, heq] with d hd heqd
    rw [← heqd]
    exact hd
  · intro h
    filter_upwards [h, heq] with d hd heqd
    rw [heqd]
    exact hd

/-- One field base change with Hilbert polynomial `P` determines the Hilbert polynomial
at every field-valued point of a local affine base. -/
theorem hasFiberwiseHilbertPolynomial_of_baseChange [IsLocalRing R]
    (H : Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange Q)
    (K : Type u) [Field K] (f : R →+* K) (P : Polynomial ℚ)
    (h : HasHilbertPolynomialOver
      (Modules.projectiveSpaceBaseChangeOfRingHom Q f) P) :
    HasFiberwiseHilbertPolynomial Q P := by
  intro L hL s
  letI : Field L := hL.toField
  obtain ⟨g, rfl⟩ := Spec.map_surjective s
  exact (H.hasHilbertPolynomialOver_baseChange_iff K L f g.hom P).mp h

/-- The canonical generic fibre of a sheaf over a DVR determines all its fibrewise
Hilbert polynomials as soon as eventual finite-projective `H⁰` base change is known. -/
theorem hasFiberwiseHilbertPolynomial_of_fractionRing
    [IsDomain R] [IsDiscreteValuationRing R]
    (H : Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange Q)
    (P : Polynomial ℚ)
    (h : HasHilbertPolynomialOver
      (Modules.projectiveSpaceBaseChangeOfRingHom Q
        (algebraMap R (FractionRing R))) P) :
    HasFiberwiseHilbertPolynomial Q P :=
  H.hasFiberwiseHilbertPolynomial_of_baseChange
    (FractionRing R) (algebraMap R (FractionRing R)) P h

end Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange

/-- On projective space over a field, a fibrewise Hilbert-polynomial assertion implies
the assertion for the sheaf itself. -/
theorem HasFiberwiseHilbertPolynomial.hasHilbertPolynomialOver
    {n : ℕ} {K : CommRingCat.{u}} (hK : IsField K)
    {Q : (projectiveSpaceOver n (Spec K)).Modules} {P : Polynomial ℚ}
    (h : HasFiberwiseHilbertPolynomial Q P) : HasHilbertPolynomialOver Q P := by
  letI : Field K := hK.toField
  have hId := h K hK (𝟙 (Spec K))
  have hmap : projectiveSpaceOverMap n (𝟙 (Spec K)) =
      𝟙 (projectiveSpaceOver n (Spec K)) := by
    apply Limits.pullback.hom_ext
    · change projectiveSpaceOverMap n (𝟙 (Spec K)) ≫
          projectiveSpaceOverπ n (Spec K) = projectiveSpaceOverπ n (Spec K)
      rw [projectiveSpaceOverMap_π]
      simp
    · change projectiveSpaceOverMap n (𝟙 (Spec K)) ≫
          Limits.pullback.snd (specULiftZIsTerminal.from (Spec K))
            (specULiftZIsTerminal.from (projectiveSpace n)) =
        Limits.pullback.snd (specULiftZIsTerminal.from (Spec K))
          (specULiftZIsTerminal.from (projectiveSpace n))
      exact projectiveSpaceOverMap_absolute_snd n (𝟙 (Spec K))
  let e := (Modules.pullbackCongr hmap).app Q ≪≫
    (Modules.pullbackId (projectiveSpaceOver n (Spec K))).app Q
  exact HasHilbertPolynomialOver.iso e hId

/-- Fibrewise Hilbert polynomial is invariant under an isomorphism of sheaves. -/
theorem HasFiberwiseHilbertPolynomial.of_iso
    {n : ℕ} {T : Scheme.{u}}
    {Q Q' : (projectiveSpaceOver n T).Modules} {P : Polynomial ℚ}
    (e : Q ≅ Q') (h : HasFiberwiseHilbertPolynomial Q P) :
    HasFiberwiseHilbertPolynomial Q' P := by
  intro K hK s
  apply HasHilbertPolynomialOver.iso
    ((Modules.pullback (projectiveSpaceOverMap n s)).mapIso e)
  exact h K hK s

namespace Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange

/-- A fibrewise Hilbert-polynomial assertion on any sheaf identified with one field base
change determines the Hilbert polynomial on every fibre of a local affine base.  This is
the form directly used for the generic restriction of a Quot datum. -/
theorem hasFiberwiseHilbertPolynomial_of_baseChange_iso
    {n : ℕ} {R : Type u} [CommRing R] [IsLocalRing R]
    {Q : (projectiveSpaceOver n (Spec (.of R))).Modules}
    (H : Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange Q)
    (K : Type u) [Field K] (f : R →+* K)
    (QK : (projectiveSpaceOver n (Spec (.of K))).Modules)
    (e : QK ≅ Modules.projectiveSpaceBaseChangeOfRingHom Q f)
    (P : Polynomial ℚ) (h : HasFiberwiseHilbertPolynomial QK P) :
    HasFiberwiseHilbertPolynomial Q P := by
  apply H.hasFiberwiseHilbertPolynomial_of_baseChange K f P
  apply HasHilbertPolynomialOver.iso e
  exact h.hasHilbertPolynomialOver (Field.toIsField K)

end Modules.HasEventualFiniteProjectiveGlobalSectionsBaseChange

end AlgebraicGeometry.Scheme
