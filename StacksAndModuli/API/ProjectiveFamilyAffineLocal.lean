module

public import StacksAndModuli.API.DVRHilbertPolynomial
public import StacksAndModuli.API.FlatOverDescent
public import StacksAndModuli.API.PushforwardProjectiveRank

/-!
# Affine-local tests for projective families

This file packages two base-locality statements in the form needed by projective
flattening arguments.  Relative flatness of a quasicoherent sheaf on relative projective
space descends from the affine cover of the base, and a fibrewise Hilbert polynomial can
be tested after pullback to every affine open of the base.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme

namespace Modules

/-- Relative flatness of a quasicoherent sheaf on relative projective space can be
checked after pullback to the members of the canonical affine cover of the base. -/
theorem FlatOver.of_affineCover_projectiveSpace
    {n : ℕ} {T : Scheme.{u}}
    {Q : (projectiveSpaceOver n T).Modules} [Q.IsQuasicoherent]
    (h : ∀ i,
      ((pullback (projectiveSpaceOverMap n (T.affineCover.f i))).obj Q).FlatOver
        (projectiveSpaceOverπ n (T.affineCover.X i))) :
    Q.FlatOver (projectiveSpaceOverπ n T) := by
  let R : Sieve T := Sieve.generate T.affineCover.presieve₀
  apply FlatOver.of_etale_sieve (projectiveSpaceOverπ n T) Q R
  · apply Scheme.zariskiTopology_le_etaleTopology
    exact Precoverage.generate_mem_toGrothendieck T.affineCover.mem₀
  · intro f
    let q := f.obj.hom
    obtain ⟨Y, a, b, ⟨i⟩, hab⟩ := f.property
    let Qᵢ := (pullback
      (projectiveSpaceOverMap n (T.affineCover.f i))).obj Q
    have ha : ((pullback (projectiveSpaceOverMap n a)).obj Qᵢ).FlatOver
        (projectiveSpaceOverπ n f.obj.left) :=
      FlatOver.pullback_of_isPullback
        (projectiveSpaceOverMap n a)
        (projectiveSpaceOverπ n f.obj.left)
        (projectiveSpaceOverπ n (T.affineCover.X i)) a
        (isPullback_projectiveSpaceOverMap n a).flip Qᵢ (h i)
    let E : (pullback (projectiveSpaceOverMap n a)).obj Qᵢ ≅
        (pullback (projectiveSpaceOverMap n q)).obj Q :=
      (pullbackComp
        (projectiveSpaceOverMap n a)
        (projectiveSpaceOverMap n (T.affineCover.f i))).app Q ≪≫
      (pullbackCongr
        (projectiveSpaceOverMap_comp n a (T.affineCover.f i))).app Q ≪≫
      (pullbackCongr
        (congrArg (projectiveSpaceOverMap n) hab)).app Q
    have hq : ((pullback (projectiveSpaceOverMap n q)).obj Q).FlatOver
        (projectiveSpaceOverπ n f.obj.left) :=
      FlatOver.of_iso E ha
    exact FlatOver.canonical_pullback_of_isPullback
      (projectiveSpaceOverMap n q)
      (projectiveSpaceOverπ n f.obj.left)
      (projectiveSpaceOverπ n T) q
      (isPullback_projectiveSpaceOverMap n q).flip Q hq

end Modules

/-- A fibrewise Hilbert polynomial can be checked after pullback to every affine open
subscheme of the base. -/
theorem HasFiberwiseHilbertPolynomial.of_affineOpen_pullbacks
    {n : ℕ} {T : Scheme.{u}}
    {Q : (projectiveSpaceOver n T).Modules} {P : Polynomial ℚ}
    (h : ∀ U : T.affineOpens,
      HasFiberwiseHilbertPolynomial
        ((Modules.pullback (projectiveSpaceOverMap n U.1.ι)).obj Q) P) :
    HasFiberwiseHilbertPolynomial Q P := by
  intro K hK s
  letI : Field K := hK.toField
  letI : Subsingleton (PrimeSpectrum K) :=
    PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mpr hK
  letI : Subsingleton (Spec K) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let y : Spec K := IsLocalRing.closedPoint K
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (s y)) isOpen_univ
  let U : T.affineOpens := ⟨V, hV⟩
  have hsrange : Set.range s ⊆ Set.range U.1.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : z = y := Subsingleton.elim _ _
    subst z
    exact ⟨⟨s y, hyV⟩, rfl⟩
  let t : Spec K ⟶ U.1.toScheme := IsOpenImmersion.lift U.1.ι s hsrange
  have ht : t ≫ U.1.ι = s := IsOpenImmersion.lift_fac _ _ _
  let E₀ := (Modules.pullbackComp
    (projectiveSpaceOverMap n t)
    (projectiveSpaceOverMap n U.1.ι)).app Q
  let E₁ := (Modules.pullbackCongr
    (projectiveSpaceOverMap_comp n t U.1.ι)).app Q
  let E₂ := (Modules.pullbackCongr
    (congrArg (projectiveSpaceOverMap n) ht)).app Q
  apply HasHilbertPolynomialOver.iso (E₀ ≪≫ E₁ ≪≫ E₂)
  exact h U K hK t

end AlgebraicGeometry.Scheme

end

end
