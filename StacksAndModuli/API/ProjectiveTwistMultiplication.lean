module

public import StacksAndModuli.API.ProjectiveTwistBaseChange
public import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Multiplication of twists on polynomial Proj

On polynomial projective space, the canonical multiplication morphism
`O(a) ⊗ O(b) ⟶ O(a + b)` is an isomorphism.  The proof checks the underlying
presheaf multiplication on the standard coordinate cover and then uses that
module sheafification inverts local equivalences.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CategoryTheory.MonoidalCategory TopologicalSpace Opposite
open ProjectiveSpectrum

universe u

namespace TopCat.Presheaf

private theorem locallyBijective_of_bijective_app_iSup_eq_top
    {X : TopCat.{u}} {I : Type u} {P Q : X.Presheaf Ab.{u}}
    (m : P ⟶ Q) (U : I → Opens X) (hU : ⨆ i, U i = ⊤)
    (hbij : ∀ (i : I) (V : Opens X), V ≤ U i →
      Function.Bijective (m.app (.op V))) :
    CategoryTheory.Presheaf.IsLocallyInjective
        (Opens.grothendieckTopology X) m ∧
      CategoryTheory.Presheaf.IsLocallySurjective
        (Opens.grothendieckTopology X) m := by
  constructor
  · constructor
    intro W s t h x hxW
    have hxcover : x ∈ ⨆ i, U i := by rw [hU]; trivial
    rw [Opens.mem_iSup] at hxcover
    obtain ⟨i, hxi⟩ := hxcover
    let V := W.unop ⊓ U i
    let k : V ⟶ W.unop := homOfLE inf_le_left
    refine ⟨V, k, ?_, ⟨hxW, hxi⟩⟩
    apply (hbij i V inf_le_right).1
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]
  · apply (isLocallySurjective_iff (X := X) m).2
    intro W t x hxW
    have hxcover : x ∈ ⨆ i, U i := by rw [hU]; trivial
    rw [Opens.mem_iSup] at hxcover
    obtain ⟨i, hxi⟩ := hxcover
    let V := W ⊓ U i
    let k : V ⟶ W := homOfLE inf_le_left
    obtain ⟨s, hs⟩ := (hbij i V inf_le_right).2 ((Q.map k.op) t)
    exact ⟨V, inf_le_left, ⟨s, hs⟩, ⟨hxW, hxi⟩⟩

end TopCat.Presheaf

namespace AlgebraicGeometry.Scheme.Modules

/-- The adjoint of a local equivalence from a module presheaf to an underlying
module sheaf is an isomorphism after sheafification. -/
theorem sheafificationAdjunction_homEquiv_symm_isIso_of_localEquivalence
    {X : Scheme.{u}} {P : X.PresheafOfModules} {F : X.Modules}
    (m : P ⟶ F.val) (hm : moduleLocalEquivalences X m) :
    IsIso (((PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).homEquiv P F).symm m) := by
  let sh := sheafification X
  let W := moduleLocalEquivalences X
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)
  let _ : IsIso (sh.map m) := Localization.inverts sh W m hm
  let _ : IsIso (adj.counit.app F) := inferInstance
  change IsIso (sh.map m ≫ adj.counit.app F)
  infer_instance

end AlgebraicGeometry.Scheme.Modules

namespace ProjectiveSpectrum.Twist

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] (i : Type) (a b : ℤ)

set_option maxHeartbeats 3200000 in
-- Elaborating the local-equivalence comparison unfolds both the tensor presheaf and sheafification.
private theorem polynomialMultiplyPresheafHom_mem_localEquivalences :
    ((Opens.grothendieckTopology
      (Proj (MvPolynomial.homogeneousSubmodule i R))).W.inverseImage
        (PresheafOfModules.toPresheaf
          (Proj (MvPolynomial.homogeneousSubmodule i R)).ringCatSheaf.obj))
      (multiplyPresheafHom
        (MvPolynomial.homogeneousSubmodule i R) a b) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule i R
  let m := multiplyPresheafHom 𝒜 a b
  let P := (PresheafOfModules.toPresheaf (Proj 𝒜).ringCatSheaf.obj).obj
    ((twist 𝒜 a).val ⊗ (twist 𝒜 b).val)
  let Q := (PresheafOfModules.toPresheaf (Proj 𝒜).ringCatSheaf.obj).obj
    (twist 𝒜 (a + b)).val
  let mab : P ⟶ Q :=
    (PresheafOfModules.toPresheaf (Proj 𝒜).ringCatSheaf.obj).map m
  let U (j : ULift.{u} i) : (Proj 𝒜).Opens :=
    Proj.basicOpen 𝒜 (MvPolynomial.X j.down)
  let hX (j : ULift.{u} i) : MvPolynomial.X j.down ∈ 𝒜 1 :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_X R j.down)
  have hU : ⨆ j, U j = ⊤ := by
    dsimp [U, 𝒜]
    rw [iSup_ulift]
    exact polynomialCoordinateCover_iSup_eq_top (R := R) i
  have hbij : ∀ (j : ULift.{u} i) (V : (Proj 𝒜).Opens), V ≤ U j →
      Function.Bijective (mab.app (.op V)) := by
    intro j V hV
    change Function.Bijective
      (TensorProduct.lift (mulSectionsBilinear 𝒜 a b (.op V)))
    exact bijective_tensorLift_mulSections 𝒜 (hX j) a b (.op V) hV
  have hlocal := TopCat.Presheaf.locallyBijective_of_bijective_app_iSup_eq_top
    mab U hU hbij
  change (Opens.grothendieckTopology (Proj 𝒜)).W mab
  rw [(Opens.grothendieckTopology (Proj 𝒜)).W_iff_isLocallyBijective]
  exact hlocal

/-- On polynomial `Proj`, the canonical multiplication morphism
`O(a) ⊗ O(b) ⟶ O(a + b)` is an isomorphism for all integer twists. -/
theorem polynomial_multiplyHom_isIso : IsIso (multiplyHom
    (MvPolynomial.homogeneousSubmodule i R) a b) := by
  let 𝒜 := MvPolynomial.homogeneousSubmodule i R
  let m := multiplyPresheafHom 𝒜 a b
  exact Scheme.Modules.sheafificationAdjunction_homEquiv_symm_isIso_of_localEquivalence m
    (polynomialMultiplyPresheafHom_mem_localEquivalences i a b)

/-- The multiplication isomorphism `O(a) ⊗ O(b) ≅ O(a + b)` on polynomial `Proj`. -/
noncomputable def polynomialMultiplyIso :
    Scheme.Modules.tensor
        (twist (MvPolynomial.homogeneousSubmodule i R) a)
        (twist (MvPolynomial.homogeneousSubmodule i R) b) ≅
      twist (MvPolynomial.homogeneousSubmodule i R) (a + b) :=
  @asIso _ _ _ _ (multiplyHom
    (MvPolynomial.homogeneousSubmodule i R) a b)
      (polynomial_multiplyHom_isIso i a b)

end ProjectiveSpectrum.Twist
