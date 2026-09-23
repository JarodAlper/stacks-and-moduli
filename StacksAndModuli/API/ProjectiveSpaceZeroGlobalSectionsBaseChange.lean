module

public import StacksAndModuli.API.AffineOpenGlobalSectionsBaseChange
public import StacksAndModuli.API.ProjectiveSpaceZeroGrassmannian

/-!
# Global-sections base change on relative projective zero-space

Relative projective zero-space is isomorphic to its base, so it is affine over an
arbitrary commutative ring.  Consequently global sections of every quasicoherent module
on relative `P⁰` commute with arbitrary scalar extension; no flatness hypothesis on the
coefficient-ring map is needed.

The equivalence in this file is the canonical scalar-extension map induced by the
pullback-adjunction unit.  Its bijectivity follows from the affine cartesian-square base
change theorem.  The projective-space square is recognized as cartesian by
`IsPullback.of_vert_isIso`, using `projectiveSpaceOverZeroIso` on both vertical maps.

Main declaration:

* `AlgebraicGeometry.Scheme.projectiveSpaceZeroGlobalSectionsBaseChangeLinearEquiv`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory TensorProduct
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The coefficient-change square for relative projective zero-space is cartesian.  Both
vertical structure maps are isomorphisms by `projectiveSpaceOverZeroIso`. -/
theorem projectiveSpaceOverMap_zero_isPullback
    {R K : Type u} [CommRing R] [CommRing K] (f : R →+* K) :
    IsPullback
      (projectiveSpaceOverMap 0 (Spec.map (CommRingCat.ofHom f)))
      (projectiveSpaceOverπ 0 (Spec (.of K)))
      (projectiveSpaceOverπ 0 (Spec (.of R)))
      (Spec.map (CommRingCat.ofHom f)) := by
  let _ : IsIso (projectiveSpaceOverπ 0 (Spec (.of R))) := by
    rw [← projectiveSpaceOverZeroIso_hom]
    infer_instance
  let _ : IsIso (projectiveSpaceOverπ 0 (Spec (.of K))) := by
    rw [← projectiveSpaceOverZeroIso_hom]
    infer_instance
  exact IsPullback.of_vert_isIso
    ⟨projectiveSpaceOverMap_π 0 (Spec.map (CommRingCat.ofHom f))⟩

/-- Global sections of a quasicoherent module on relative projective zero-space commute
with scalar extension along an arbitrary homomorphism of commutative rings.  The
underlying linear map is `Modules.pullbackGlobalSectionsBaseChangeLinearMap`. -/
noncomputable def projectiveSpaceZeroGlobalSectionsBaseChangeLinearEquiv
    {R K : Type u} [CommRing R] [CommRing K] (f : R →+* K)
    (Q : (projectiveSpaceOver 0 (Spec (.of R))).Modules)
    [Q.IsQuasicoherent] :
    let g := projectiveSpaceOverMap 0 (Spec.map (CommRingCat.ofHom f))
    let N := (Modules.pullback g).obj Q
    let pR := projectiveSpaceOverπ 0 (Spec (.of R))
    let pK := projectiveSpaceOverπ 0 (Spec (.of K))
    letI : Algebra R K := f.toAlgebra
    letI : Module R Γ(Q, ⊤) := Modules.globalSectionsModule pR Q
    letI : Module K Γ(N, ⊤) := Modules.globalSectionsModule pK N
    K ⊗[R] Γ(Q, ⊤) ≃ₗ[K] Γ(N, ⊤) := by
  let φ : CommRingCat.of R ⟶ CommRingCat.of K := CommRingCat.ofHom f
  let g := projectiveSpaceOverMap 0 (Spec.map φ)
  let pR := projectiveSpaceOverπ 0 (Spec (.of R))
  let pK := projectiveSpaceOverπ 0 (Spec (.of K))
  let N := (Modules.pullback g).obj Q
  letI : Algebra R K := f.toAlgebra
  letI : Module R Γ(Q, ⊤) := Modules.globalSectionsModule pR Q
  letI : Module K Γ(N, ⊤) := Modules.globalSectionsModule pK N
  letI : IsAffine (projectiveSpaceOver 0 (Spec (.of R))) :=
    IsAffine.of_isIso (projectiveSpaceOverZeroIso _).hom
  letI : IsAffine (projectiveSpaceOver 0 (Spec (.of K))) :=
    IsAffine.of_isIso (projectiveSpaceOverZeroIso _).hom
  let h : IsPullback g pK pR (Spec.map φ) :=
    projectiveSpaceOverMap_zero_isPullback f
  exact LinearEquiv.ofBijective
    (Modules.pullbackGlobalSectionsBaseChangeLinearMap φ g pR pK h.w Q)
    (Modules.pullbackGlobalSectionsBaseChangeLinearMap_bijective_of_isPullback
      φ g pR pK h Q)

/-- The underlying map of the `P⁰` global-sections base-change equivalence is the
canonical scalar-extension map induced by the pullback-adjunction unit. -/
theorem projectiveSpaceZeroGlobalSectionsBaseChangeLinearEquiv_toLinearMap
    {R K : Type u} [CommRing R] [CommRing K] (f : R →+* K)
    (Q : (projectiveSpaceOver 0 (Spec (.of R))).Modules)
    [Q.IsQuasicoherent] :
    let φ : CommRingCat.of R ⟶ CommRingCat.of K := CommRingCat.ofHom f
    let g := projectiveSpaceOverMap 0 (Spec.map φ)
    let N := (Modules.pullback g).obj Q
    let pR := projectiveSpaceOverπ 0 (Spec (.of R))
    let pK := projectiveSpaceOverπ 0 (Spec (.of K))
    let h : IsPullback g pK pR (Spec.map φ) :=
      projectiveSpaceOverMap_zero_isPullback f
    letI : Algebra R K := f.toAlgebra
    letI : Module R Γ(Q, ⊤) := Modules.globalSectionsModule pR Q
    letI : Module K Γ(N, ⊤) := Modules.globalSectionsModule pK N
    (projectiveSpaceZeroGlobalSectionsBaseChangeLinearEquiv f Q).toLinearMap =
      Modules.pullbackGlobalSectionsBaseChangeLinearMap φ g pR pK h.w Q := by
  rfl

end AlgebraicGeometry.Scheme

end
