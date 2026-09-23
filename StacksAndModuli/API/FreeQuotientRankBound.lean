module

public import StacksAndModuli.«Section2.1-Intro».«part2.1.2-the-grassmannian-functor»

/-!
# Rank bounds for finite free quotients

A rank-`q` vector-bundle quotient of a free sheaf of rank `r` over a nonempty
scheme forces `q ≤ r`.  The proof pulls the quotient to a residue field, passes
to the resulting surjection of finite-dimensional vector spaces on the affine
spectrum, and compares dimensions.

This also shows directly that the relative Grassmannian functor `Gr(q, r)` is
empty on every nonempty test scheme when `r < q`.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

/-- A rank-`q` quotient of a free rank-`r` sheaf over the spectrum of a field
forces `q ≤ r`. -/
lemma FreeQuotient.rank_le_of_field
    {K : Type u} [Field K] {q r : ℕ}
    (x : FreeQuotient q (ULift.{u} (Fin r)) (Spec (.of K))) : q ≤ r := by
  let t : Spec (.of K) := default
  obtain ⟨U, htU, hfin, hproj, hrank⟩ := x.isProjectiveOfRank t
  have hU : U.1 = ⊤ := by
    apply top_unique
    intro y _
    rw [show y = t from Subsingleton.elim _ _]
    exact htU
  rw [hU] at hfin hproj hrank
  obtain ⟨_, _, hrank'⟩ :=
    moduleSpecΓFunctor_finite_projective_rank_of_top (R := CommRingCat.of K)
      x.Q hfin hproj hrank
  have htarget : Module.finrank (CommRingCat.of K)
      ((moduleSpecΓFunctor (R := CommRingCat.of K)).obj x.Q) = q := by
    have hp := hrank' (default : PrimeSpectrum (CommRingCat.of K))
    simpa [Module.rankAtStalk_eq_finrank_of_free] using hp
  calc
    q = Module.finrank (CommRingCat.of K)
        ((moduleSpecΓFunctor (R := CommRingCat.of K)).obj x.Q) := htarget.symm
    _ ≤ Module.finrank (CommRingCat.of K)
        (ULift.{u} (Fin r) →₀ (CommRingCat.of K)) :=
      x.moduleMap.finrank_le_finrank_of_surjective x.moduleMap_surjective
    _ = r := by simp

/-- A rank-`q` quotient of a free rank-`r` sheaf over any nonempty parameter
scheme forces `q ≤ r`. -/
lemma PullbackQuotient.rank_le_of_nonempty
    {S : Scheme.{u}} {q r : ℕ} {T : Over S}
    (x : PullbackQuotient q
      (SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin r))) T)
    (hT : Nonempty T.left) : q ≤ r := by
  let t : T.left := Classical.choice hT
  let Tt : Over S := Over.mk (T.left.fromSpecResidueField t ≫ T.hom)
  let g : Tt ⟶ T := Over.homMk (T.left.fromSpecResidueField t) rfl
  exact (x.pullback g).toFreeQuotient.rank_le_of_field

/-- If `r < q`, the relative Grassmannian of rank-`q` quotients of a free
rank-`r` sheaf has no points over a nonempty test scheme. -/
theorem grassmannianOverFunctor_isEmpty_of_lt
    (S : Scheme.{u}) (q r : ℕ) (hqr : r < q) (T : Over S)
    (hT : Nonempty T.left) :
    IsEmpty ((grassmannianOverFunctor q
      (SheafOfModules.free (R := S.ringCatSheaf)
        (ULift.{u} (Fin r)))).obj (op T)) := by
  constructor
  intro z
  change Quotient (PullbackQuotient.setoid q
    (SheafOfModules.free (R := S.ringCatSheaf)
      (ULift.{u} (Fin r))) T) at z
  obtain ⟨x, rfl⟩ := Quotient.exists_rep z
  exact (Nat.not_le_of_lt hqr) (x.rank_le_of_nonempty hT)

end AlgebraicGeometry.Scheme.Modules

end
