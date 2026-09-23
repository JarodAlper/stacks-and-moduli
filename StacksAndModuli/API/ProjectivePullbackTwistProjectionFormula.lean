module

public import StacksAndModuli.API.SchemeModulesAffineFiniteLocallyFreeProjectionFormula
public import StacksAndModuli.API.TwistedFreeQuotGrassmannianRelationKernel

/-!
# Projection formula for pullback coefficients on projective space

This file names the canonical map

`K ⊗ π_* ᵏ(t) ⟶ π_*(π^*K ⊗ ᵏ(t))`

for relative projective space and records its finite-free case.  The twists `0` and `1`
are the coefficient calculation required by the two-term Grassmannian reconstruction.
The universal relation kernel is finite locally free by the companion relation-kernel API,
and the calculation therefore holds after restriction to every affine base.  Promoting
these local calculations to the universal kernel globally requires compatibility of this
canonical map with restriction to open subschemes.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {S : Scheme.{u}}

/-- The canonical projection-formula map for a pullback coefficient sheaf tensored with
a twist on relative projective space. -/
noncomputable def projectivePullbackTwistProjectionFormulaHom
    (n : ℕ) (S : Scheme.{u}) (K : S.Modules) (t : ℤ) :
    tensor K
        ((pushforward (Scheme.projectiveSpaceOverπ n S)).obj
          (Scheme.projectiveSpaceOverTwist n S t)) ⟶
      (pushforward (Scheme.projectiveSpaceOverπ n S)).obj
        (Scheme.projectiveSpaceOverTwistModule
          ((pullback (Scheme.projectiveSpaceOverπ n S)).obj K) t) :=
  projectionFormulaHom (Scheme.projectiveSpaceOverπ n S) K
    (Scheme.projectiveSpaceOverTwist n S t)

/-- Invertibility of the canonical projection-formula map for one projective twist. -/
abbrev ProjectivePullbackTwistProjectionFormula
    (n : ℕ) (S : Scheme.{u}) (K : S.Modules) (t : ℤ) : Prop :=
  IsIso (projectivePullbackTwistProjectionFormulaHom n S K t)

/-- The two low-twist projection formulas used by the two-term reconstructed quotient. -/
abbrev ProjectivePullbackZeroOneProjectionFormula
    (n : ℕ) (S : Scheme.{u}) (K : S.Modules) : Prop :=
  ProjectivePullbackTwistProjectionFormula n S K 0 ∧
    ProjectivePullbackTwistProjectionFormula n S K 1

/-- The canonical projective pullback--twist projection formula holds for finite free
coefficient sheaves, in every twist. -/
theorem projectivePullbackTwistProjectionFormulaHom_isIso_free
    {J : Type u} [Finite J] (n : ℕ) (S : Scheme.{u}) (t : ℤ) :
    IsIso (projectivePullbackTwistProjectionFormulaHom n S
      (SheafOfModules.free (R := S.ringCatSheaf) J) t) := by
  change IsIso (projectionFormulaHom (Scheme.projectiveSpaceOverπ n S)
    (SheafOfModules.free (R := S.ringCatSheaf) J)
    (Scheme.projectiveSpaceOverTwist n S t))
  exact projectionFormulaHom_isIso_free (Scheme.projectiveSpaceOverπ n S)
    (Scheme.projectiveSpaceOverTwist n S t)

/-- Finite free coefficient sheaves satisfy both low-twist projection formulas. -/
theorem projectivePullbackZeroOneProjectionFormula_free
    {J : Type u} [Finite J] (n : ℕ) (S : Scheme.{u}) :
    ProjectivePullbackZeroOneProjectionFormula n S
      (SheafOfModules.free (R := S.ringCatSheaf) J) := by
  constructor
  · exact projectivePullbackTwistProjectionFormulaHom_isIso_free n S 0
  · exact projectivePullbackTwistProjectionFormulaHom_isIso_free n S 1

/-- Over an affine base, the canonical projective pullback--twist projection formula
holds for finite locally free quasicoherent coefficients. -/
theorem projectivePullbackTwistProjectionFormulaHom_isIso_of_isFiniteLocallyFree_of_isAffine
    [IsAffine S] {K : S.Modules} [K.IsQuasicoherent]
    (hK : IsFiniteLocallyFree K) (n : ℕ) (t : ℤ) :
    IsIso (projectivePullbackTwistProjectionFormulaHom n S K t) := by
  change IsIso (projectionFormulaHom (Scheme.projectiveSpaceOverπ n S) K
    (Scheme.projectiveSpaceOverTwist n S t))
  exact projectionFormulaHom_isIso_of_isFiniteLocallyFree_of_isAffine
    (Scheme.projectiveSpaceOverπ n S) hK
    (Scheme.projectiveSpaceOverTwist n S t)

/-- Finite locally free quasicoherent coefficients over an affine base satisfy both
low-twist projection formulas. -/
theorem projectivePullbackZeroOneProjectionFormula_of_isFiniteLocallyFree_of_isAffine
    [IsAffine S] {K : S.Modules} [K.IsQuasicoherent]
    (hK : IsFiniteLocallyFree K) (n : ℕ) :
    ProjectivePullbackZeroOneProjectionFormula n S K := by
  constructor
  · exact
      projectivePullbackTwistProjectionFormulaHom_isIso_of_isFiniteLocallyFree_of_isAffine
        hK n 0
  · exact
      projectivePullbackTwistProjectionFormulaHom_isIso_of_isFiniteLocallyFree_of_isAffine
        hK n 1

/-- Pulling a finite locally free coefficient off an affine scheme preserves the
canonical projective pullback--twist projection formula in every twist, even when the
new base is not affine. -/
theorem
    projectivePullbackTwistProjectionFormulaHom_isIso_pullback_of_isFiniteLocallyFree_of_isAffine
    {S' : Scheme.{u}} [IsAffine S] (g : S' ⟶ S)
    {K : S.Modules} [K.IsQuasicoherent] (hK : IsFiniteLocallyFree K)
    (n : ℕ) (t : ℤ) :
    IsIso (projectivePullbackTwistProjectionFormulaHom n S'
      ((pullback g).obj K) t) := by
  change IsIso (projectionFormulaHom (Scheme.projectiveSpaceOverπ n S')
    ((pullback g).obj K) (Scheme.projectiveSpaceOverTwist n S' t))
  exact projectionFormulaHom_isIso_pullback_of_isFiniteLocallyFree_of_isAffine
    g (Scheme.projectiveSpaceOverπ n S') hK
      (Scheme.projectiveSpaceOverTwist n S' t)

/-- Both low-twist projection formulas survive every pullback of a finite locally
free coefficient from an affine scheme. -/
theorem
    projectivePullbackZeroOneProjectionFormula_pullback_of_isFiniteLocallyFree_of_isAffine
    {S' : Scheme.{u}} [IsAffine S] (g : S' ⟶ S)
    {K : S.Modules} [K.IsQuasicoherent] (hK : IsFiniteLocallyFree K)
    (n : ℕ) :
    ProjectivePullbackZeroOneProjectionFormula n S' ((pullback g).obj K) := by
  constructor
  · exact
      projectivePullbackTwistProjectionFormulaHom_isIso_pullback_of_isFiniteLocallyFree_of_isAffine
        g hK n 0
  · exact
      projectivePullbackTwistProjectionFormulaHom_isIso_pullback_of_isFiniteLocallyFree_of_isAffine
        g hK n 1

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}} {n r m q e : ℕ}
  {σ : ULift.{u} (Fin m) ≃
    ULift.{u} (Fin r) × Fin ((n + e).choose n)}

/-- The unresolved low-twist projection-formula assertion for the finite locally free
relation kernel in the universal Grassmannian reconstruction. -/
abbrev FreeGrassmannianUniversalRelationKernelZeroOneProjectionFormula
    (S : Scheme.{u}) (n r m q e : ℕ)
    (σ : ULift.{u} (Fin m) ≃
      ULift.{u} (Fin r) × Fin ((n + e).choose n)) : Prop :=
  Modules.ProjectivePullbackZeroOneProjectionFormula n
    (grassmannianOverRepresentation S q m).left
    (kernel (grassmannianPointMonomialQuotientMap
      (n := n) (r := r) (q := q) (e := e) (σ := σ)
      (grassmannianOverRepresentation S q m)
      (freeGrassmannianUniversalPoint S q m)))

/-- On an affine test scheme, the relation kernel of every Grassmannian point satisfies
the two low-twist projection formulas required by the reconstruction. -/
theorem grassmannianPointMonomialQuotientMap_kernel_zeroOneProjectionFormula_of_isAffine
    (T : Over S) [IsAffine T.left]
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m) :
    Modules.ProjectivePullbackZeroOneProjectionFormula n T.left
      (kernel (grassmannianPointMonomialQuotientMap
        (n := n) (r := r) (q := q) (e := e) (σ := σ) T g)) := by
  let x := grassmannianPointFreeQuotient (q := q) T g
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  letI : (kernel (grassmannianPointMonomialQuotientMap
      (n := n) (r := r) (q := q) (e := e) (σ := σ) T g)).IsQuasicoherent :=
    Modules.kernel_isQuasicoherent _
  exact
    Modules.projectivePullbackZeroOneProjectionFormula_of_isFiniteLocallyFree_of_isAffine
      (grassmannianPointMonomialQuotientMap_kernel_isFiniteLocallyFree
        (n := n) (r := r) (q := q) (e := e) (σ := σ) T g) n

/-- The low-twist projection formulas for the relation kernel of an affine
Grassmannian point remain valid after every further base change. -/
theorem
    grassmannianPointMonomialQuotientMap_kernel_zeroOneProjectionFormula_pullback_of_isAffine
    (T : Over S) [IsAffine T.left]
    (g : uliftYoneda.{u + 1}.obj T ⟶
      Modules.grassmannianFunctorOver S q m)
    {T' : Scheme.{u}} (a : T' ⟶ T.left) :
    Modules.ProjectivePullbackZeroOneProjectionFormula n T'
      ((Modules.pullback a).obj
        (kernel (grassmannianPointMonomialQuotientMap
          (n := n) (r := r) (q := q) (e := e) (σ := σ) T g))) := by
  let x := grassmannianPointFreeQuotient (q := q) T g
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  letI : (kernel (grassmannianPointMonomialQuotientMap
      (n := n) (r := r) (q := q) (e := e) (σ := σ) T g)).IsQuasicoherent :=
    Modules.kernel_isQuasicoherent _
  exact
    Modules.projectivePullbackZeroOneProjectionFormula_pullback_of_isFiniteLocallyFree_of_isAffine
      a (grassmannianPointMonomialQuotientMap_kernel_isFiniteLocallyFree
        (n := n) (r := r) (q := q) (e := e) (σ := σ) T g) n

end AlgebraicGeometry.Scheme

end

end
