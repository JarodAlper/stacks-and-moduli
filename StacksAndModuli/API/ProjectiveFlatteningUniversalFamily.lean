module

public import StacksAndModuli.API.ProjectiveFlatteningLocus
public import StacksAndModuli.API.ProjectiveSpaceOverMapIso

/-!
# The projective flattening locus of an already-flat family

If a quasicoherent family on relative projective space is already flat over its base and
has the prescribed fibrewise Hilbert polynomial, then every base change has the same two
properties.  Consequently its projective flattening functor is terminal, and its finite-rank
presentation is the empty conjunction.

This is the degenerate endpoint of projective flattening, but it is useful in fibre
arguments: after restricting a reconstructed quotient to its flattening locus, no further
rank conditions remain.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.projectiveFlatteningFunctorIsoTerminal`;
* `AlgebraicGeometry.Scheme.Modules.projectiveFlatteningHasFiniteRankPresentation_of_flat`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {T : Scheme.{u}} (n : ℕ)
variable (Q : (Scheme.projectiveSpaceOver n T).Modules) (P : Polynomial ℚ)

/-- Pulling a projective family back along the identity object of the slice recovers the
original family. -/
noncomputable def projectiveFamilyAtIdentityIso :
    projectiveFamilyAt n Q (Over.mk (𝟙 T)) ≅ Q :=
  (Scheme.Modules.pullbackCongr (Scheme.projectiveSpaceOverMap_id n T)).app Q ≪≫
    (Scheme.Modules.pullbackId (Scheme.projectiveSpaceOver n T)).app Q

variable [Q.IsQuasicoherent]

/-- Values of the projective flattening functor are proof-valued. -/
lemma projectiveFlatteningFunctor_subsingleton (A : (Over T)ᵒᵖ) :
    Subsingleton ((projectiveFlatteningFunctor n Q (P := P)).obj A) := by
  refine ⟨fun x y ↦ ?_⟩
  apply ULift.ext
  exact Subsingleton.elim _ _

/-- The unique point of the zero-fold conjunction at a test object. -/
noncomputable def emptyFlatRankConjunctionPoint (A : (Over T)ᵒᵖ) :
    (finProdFunctorLarge
      (fun i : Fin 0 ↦ flatRankFunctorOver (Fin.elim0 i) 0 ⋙ uliftFunctor.{u + 1})).obj A :=
  ULift.up (Over.homMk A.unop.hom (by simp) : A.unop ⟶ Over.mk (𝟙 T))

/-- The zero-fold conjunction is subsingleton-valued. -/
lemma emptyFlatRankConjunction_subsingleton (A : (Over T)ᵒᵖ) :
    Subsingleton ((finProdFunctorLarge
      (fun i : Fin 0 ↦ flatRankFunctorOver (Fin.elim0 i) 0 ⋙ uliftFunctor.{u + 1})).obj A) :=
  finProdFunctorLarge_subsingleton
    (fun i : Fin 0 ↦ flatRankFunctorOver (Fin.elim0 i) 0 ⋙ uliftFunctor.{u + 1})
    (fun i ↦ Fin.elim0 i) A

/-- The canonical point of the projective flattening functor at the identity object, for an
already-flat family with the prescribed fibrewise Hilbert polynomial. -/
noncomputable def projectiveFlatteningIdentityPoint
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n T))
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q P) :
    (projectiveFlatteningFunctor n Q (P := P)).obj (op (Over.mk (𝟙 T))) := by
  refine ULift.up (PLift.up ⟨?_, ?_⟩)
  · exact Scheme.Modules.FlatOver.of_iso
      (projectiveFamilyAtIdentityIso n Q).symm hflat
  · exact Scheme.HasFiberwiseHilbertPolynomial.of_iso
      (projectiveFamilyAtIdentityIso n Q).symm hP

/-- If the original family is flat with fibrewise Hilbert polynomial `P`, its projective
flattening functor is the terminal representable functor on schemes over the base. -/
noncomputable def projectiveFlatteningFunctorIsoTerminal
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n T))
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q P) :
    finProdFunctorLarge
        (fun i : Fin 0 ↦ flatRankFunctorOver (Fin.elim0 i) 0 ⋙ uliftFunctor.{u + 1}) ≅
      projectiveFlatteningFunctor n Q (P := P) where
  hom :=
    { app := fun A ↦ ↾fun _ ↦
        (projectiveFlatteningFunctor n Q (P := P)).map
          (Over.homMk A.unop.hom (by simp) : A.unop ⟶ Over.mk (𝟙 T)).op
          (projectiveFlatteningIdentityPoint n Q P hflat hP)
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        exact (projectiveFlatteningFunctor_subsingleton n Q P B).elim _ _ }
  inv :=
    { app := fun A ↦ ↾fun _ ↦ emptyFlatRankConjunctionPoint A
      naturality := by
        intro A B g
        apply ConcreteCategory.hom_ext
        intro x
        exact (emptyFlatRankConjunction_subsingleton B).elim _ _ }
  hom_inv_id := by
    ext A x
    exact (emptyFlatRankConjunction_subsingleton A).elim _ _
  inv_hom_id := by
    ext A x
    exact (projectiveFlatteningFunctor_subsingleton n Q P A).elim _ _

/-- An already-flat projective family with fibrewise Hilbert polynomial `P` has a genuine
finite-rank presentation: the empty conjunction. -/
theorem projectiveFlatteningHasFiniteRankPresentation_of_flat
    (hflat : Q.FlatOver (Scheme.projectiveSpaceOverπ n T))
    (hP : Scheme.HasFiberwiseHilbertPolynomial Q P) :
    ProjectiveFlatteningHasFiniteRankPresentation n Q (P := P) := by
  refine ⟨{
    count := 0
    sheaf := Fin.elim0
    rank := Fin.elim0
    isQuasicoherent := fun i ↦ Fin.elim0 i
    finite := fun i ↦ Fin.elim0 i
    iso := projectiveFlatteningFunctorIsoTerminal n Q P hflat hP }⟩

end AlgebraicGeometry.Scheme.Modules

end
