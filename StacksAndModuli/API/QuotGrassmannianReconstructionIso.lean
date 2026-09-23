module

public import StacksAndModuli.API.QuotGrassmannianReconstruction

/-!
# Invariance of Grassmannian reconstruction under quotient isomorphism

The reconstructed quotient depends on a finite-free quotient only through its
kernel subobject.  This file records the categorical transport along a compatible
isomorphism of quotient targets, including compatibility with the reconstructed
quotient maps.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A compatible isomorphism of the targets of two finite-free quotient maps
induces an isomorphism of their reconstruction relation sources. -/
noncomputable def reconstructedRelationSourceIsoOfTargetIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (_he : (d : ℤ) - l = (e : ℤ)) {E E' : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (v : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E')
    (ε : E ≅ E') (hε : u ≫ ε.hom = v) :
    Modules.tensor
        ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel u))
        (projectiveSpaceOverTwist n T (-(d : ℤ))) ≅
      Modules.tensor
        ((Modules.pullback (projectiveSpaceOverπ n T)).obj (kernel v))
        (projectiveSpaceOverTwist n T (-(d : ℤ))) :=
  let k : kernel u ≅ kernel v :=
    kernel.mapIso (f := u) v (Iso.refl _) ε hε
  Modules.tensorLeftIso
    ((Modules.pullback (projectiveSpaceOverπ n T)).mapIso k)
    (projectiveSpaceOverTwist n T (-(d : ℤ)))

/-- The reconstruction relations commute with transport along a compatible
isomorphism of quotient targets. -/
lemma reconstructedRelation'_naturality_targetIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E E' : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (v : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E')
    (ε : E ≅ E') (hε : u ≫ ε.hom = v) :
    reconstructedRelation' n T l r d e he u =
      (reconstructedRelationSourceIsoOfTargetIso
        n T l r d e he u v ε hε).hom ≫
        reconstructedRelation' n T l r d e he v := by
  let k : kernel u ≅ kernel v :=
    kernel.mapIso (f := u) v (Iso.refl _) ε hε
  have hk : k.hom ≫ kernel.ι v = kernel.ι u := by
    dsimp only [k, kernel.mapIso, kernel.map]
    exact kernel.lift_ι _ _ _
  change reconstructedRelation' n T l r d e he u =
    Modules.tensorMapLeft
        ((Modules.pullback (projectiveSpaceOverπ n T)).map k.hom)
        (projectiveSpaceOverTwist n T (-(d : ℤ))) ≫
      reconstructedRelation' n T l r d e he v
  dsimp only [reconstructedRelation']
  simp only [← Category.assoc, ← Modules.tensorMapLeft_comp,
    ← Functor.map_comp, hk]

/-- Reconstruction is invariant under a compatible isomorphism of the target
of the finite-free quotient map. -/
noncomputable def reconstructedQuotientIsoOfTargetIso
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E E' : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (v : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E')
    (ε : E ≅ E') (hε : u ≫ ε.hom = v) :
    reconstructedQuotient' n T l r d e he u ≅
      reconstructedQuotient' n T l r d e he v :=
  cokernel.mapIso (f := reconstructedRelation' n T l r d e he u)
    (reconstructedRelation' n T l r d e he v)
    (reconstructedRelationSourceIsoOfTargetIso
      n T l r d e he u v ε hε)
    (Iso.refl _)
    (by
      simpa only [Iso.refl_hom, Category.comp_id] using
        reconstructedRelation'_naturality_targetIso
          n T l r d e he u v ε hε)

/-- The reconstruction isomorphism induced by a quotient-target isomorphism
commutes with the quotient maps from the twisted-free ambient sheaf. -/
@[reassoc (attr := simp)]
lemma reconstructedQuotientMap'_comp_reconstructedQuotientIsoOfTargetIso_hom
    (n : ℕ) (T : Scheme.{u}) (l : ℤ) (r : ℕ) (d e : ℕ)
    (he : (d : ℤ) - l = (e : ℤ)) {E E' : T.Modules}
    (u : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E)
    (v : SheafOfModules.free (R := T.ringCatSheaf)
      (ULift.{u} (Fin r) × Fin ((n + e).choose n)) ⟶ E')
    (ε : E ≅ E') (hε : u ≫ ε.hom = v) :
    reconstructedQuotientMap' n T l r d e he u ≫
        (reconstructedQuotientIsoOfTargetIso
          n T l r d e he u v ε hε).hom =
      reconstructedQuotientMap' n T l r d e he v := by
  dsimp only [reconstructedQuotientIsoOfTargetIso,
    reconstructedQuotientMap']
  rw [cokernel.mapIso_hom, cokernel.π_desc]
  exact Category.id_comp _

end AlgebraicGeometry.Scheme

end
