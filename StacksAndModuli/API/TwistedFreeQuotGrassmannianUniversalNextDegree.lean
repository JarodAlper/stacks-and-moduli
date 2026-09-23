module

public import StacksAndModuli.API.TwistedFreeQuotGrassmannianNextDegree
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianRelationKernel

/-!
# The universal algebraic next-degree Grassmannian module

This file specializes the finite algebraic next-degree cokernel to the universal
point of the free Grassmannian.  The resulting quasicoherent finitely presented
sheaf on the Grassmannian is the input for the single-rank projective flattening
interface.  Its arbitrary pullback is computed by the normalized pullback of the
universal finite-free quotient, without invoking projective pushforward base change.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The algebraic degree-`e+1` cokernel attached to the universal quotient on
the free Grassmannian. -/
noncomputable def freeGrassmannianUniversalNextDegreeModule
    (S : Scheme.{u}) (n r m q e : ℕ)
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    (grassmannianOverRepresentation S q m).left.Modules :=
  twistedFreeNextDegreeModule n
    (grassmannianOverRepresentation S q m).left r e
    (grassmannianPointMonomialQuotientMap
      (n := n) (r := r) (q := q) (e := e) (σ := σ)
      (grassmannianOverRepresentation S q m)
      (freeGrassmannianUniversalPoint S q m))

/-- The universal algebraic next-degree module is quasicoherent. -/
theorem freeGrassmannianUniversalNextDegreeModule_isQuasicoherent
    (S : Scheme.{u}) (n r m q e : ℕ)
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    (freeGrassmannianUniversalNextDegreeModule
      S n r m q e σ).IsQuasicoherent := by
  let G := grassmannianOverRepresentation S q m
  let x := grassmannianPointFreeQuotient (q := q) G
    (freeGrassmannianUniversalPoint S q m)
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  exact twistedFreeNextDegreeModule_isQuasicoherent n G.left r e
    (grassmannianPointMonomialQuotientMap
      (n := n) (r := r) (q := q) (e := e) (σ := σ) G
      (freeGrassmannianUniversalPoint S q m))

/-- The universal algebraic next-degree module is finitely presented. -/
theorem freeGrassmannianUniversalNextDegreeModule_isFinitePresentation
    (S : Scheme.{u}) (n r m q e : ℕ)
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n)) :
    (freeGrassmannianUniversalNextDegreeModule
      S n r m q e σ).IsFinitePresentation := by
  let G := grassmannianOverRepresentation S q m
  let x := grassmannianPointFreeQuotient (q := q) G
    (freeGrassmannianUniversalPoint S q m)
  let u₀ := grassmannianPointMonomialQuotientMap
    (n := n) (r := r) (q := q) (e := e) (σ := σ) G
    (freeGrassmannianUniversalPoint S q m)
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  letI : Epi x.π := x.epi
  let f := SheafOfModules.freeMap (R := G.left.ringCatSheaf) σ.symm
  letI : IsIso f := Modules.freeMap_isIso_of_equiv σ.symm
  letI : Epi u₀ := by
    dsimp only [u₀, grassmannianPointMonomialQuotientMap, f, x]
    infer_instance
  exact twistedFreeNextDegreeModule_isFinitePresentation n G.left r e u₀
    x.isProjectiveOfRank.isFiniteLocallyFree

/-- Arbitrary pullback of the universal algebraic next-degree module is the
next-degree module of the normalized pulled finite-free quotient. -/
noncomputable def freeGrassmannianUniversalNextDegreeModulePullbackIso
    (S : Scheme.{u}) (n r m q e : ℕ)
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n))
    {X : Scheme.{u}}
    (f : X ⟶ (grassmannianOverRepresentation S q m).left) :
    (Modules.pullback f).obj
        (freeGrassmannianUniversalNextDegreeModule S n r m q e σ) ≅
      twistedFreeNextDegreeModule n X r e
        (pullbackFreeQuotientMap f
          (grassmannianPointMonomialQuotientMap
            (n := n) (r := r) (q := q) (e := e) (σ := σ)
            (grassmannianOverRepresentation S q m)
            (freeGrassmannianUniversalPoint S q m))) := by
  let G := grassmannianOverRepresentation S q m
  let x := grassmannianPointFreeQuotient (q := q) G
    (freeGrassmannianUniversalPoint S q m)
  let u₀ := grassmannianPointMonomialQuotientMap
    (n := n) (r := r) (q := q) (e := e) (σ := σ) G
    (freeGrassmannianUniversalPoint S q m)
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  letI : Epi x.π := x.epi
  let g := SheafOfModules.freeMap (R := G.left.ringCatSheaf) σ.symm
  letI : IsIso g := Modules.freeMap_isIso_of_equiv σ.symm
  letI : Epi u₀ := by
    dsimp only [u₀, grassmannianPointMonomialQuotientMap, g, x]
    infer_instance
  exact twistedFreeNextDegreeModulePullbackIso n f r e u₀
    x.isProjectiveOfRank.isFiniteLocallyFree

end AlgebraicGeometry.Scheme

end

end
