module

public import StacksAndModuli.API.AffineAcyclic
public import StacksAndModuli.API.SheafCohomologyMayerVietorisVanishing

/-!
# Grothendieck vanishing on a quasi-compact open of an affine scheme

If a quasicoherent sheaf on `Spec R` (`R` noetherian) is restricted to an open covered by `r`
basic opens, its cohomology vanishes in every degree `≥ r`:

`Hⁿ(D(f₁) ∪ ⋯ ∪ D(f_r), M) = 0` for `n ≥ max 1 r`.

The proof is the Mayer–Vietoris induction on `r`.  The base case `r ≤ 1` is
`AlgebraicGeometry.tilde.subsingleton_HPrime_of_isQuasicoherent` (the empty union is
`D(0)`), and the inductive step splits off one basic open, whose intersection with the rest is
again a union of at most `r - 1` basic opens.

This is the affine case of Grothendieck's vanishing theorem, and it is the pattern that the
Čech computation on `ℙⁿ` runs on.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry PrimeSpectrum Limits

namespace AlgebraicGeometry.tilde

variable {R : CommRingCat.{u}} [IsNoetherianRing R]

/-- The basic-open acyclicity, restated for a positive degree rather than a successor. -/
lemma subsingleton_HPrime_basicOpen (M : (Spec R).Modules) [M.IsQuasicoherent]
    {n : ℕ} (hn : 1 ≤ n) (f : R) :
    Subsingleton
      (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M).H' n (basicOpen f)) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm]
  exact subsingleton_HPrime_of_isQuasicoherent M m f

/-- **Grothendieck vanishing on a union of finitely many basic opens.** -/
theorem subsingleton_HPrime_finsetOpen (M : (Spec R).Modules) [M.IsQuasicoherent] :
    ∀ (k : ℕ) (S : Finset R), S.card ≤ k → ∀ n : ℕ, 1 ≤ n → k ≤ n →
      Subsingleton
        (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M).H' n (finsetOpen S)) := by
  classical
  intro k
  induction k with
  | zero =>
      intro S hS n hn _
      rw [Finset.card_eq_zero.mp (Nat.le_zero.mp hS), finsetOpen_empty,
        ← PrimeSpectrum.basicOpen_zero (R := R)]
      exact subsingleton_HPrime_basicOpen M hn 0
  | succ k ih =>
      intro S hS n hn hkn
      rcases eq_or_ne S ∅ with rfl | hSne
      · rw [finsetOpen_empty, ← PrimeSpectrum.basicOpen_zero (R := R)]
        exact subsingleton_HPrime_basicOpen M hn 0
      obtain ⟨g, hg⟩ := Finset.nonempty_iff_ne_empty.mpr hSne
      set S' : Finset R := S.erase g with hS'
      have hins : insert g S' = S := Finset.insert_erase hg
      have hcard' : S'.card ≤ k := by
        have h1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨g, hg⟩
        have h2 : S'.card = S.card - 1 := Finset.card_erase_of_mem hg
        omega
      rcases eq_or_ne S' ∅ with hS'e | hS'ne
      · rw [← hins, hS'e, show insert g (∅ : Finset R) = {g} from rfl, finsetOpen_singleton]
        exact subsingleton_HPrime_basicOpen M hn g
      -- both pieces are nonempty: `n ≥ 2`
      have hk1 : 1 ≤ k := by
        have : 1 ≤ S'.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hS'ne)
        omega
      have hn2 : 2 ≤ n := by omega
      obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
      rw [← hins, finsetOpen_insert]
      refine CategoryTheory.Sheaf.subsingleton_HPrime_sup _ _ _ m (m + 1) rfl ?_ ?_ ?_
      · rw [inf_finsetOpen]
        exact ih _ (le_trans (Finset.card_image_le) hcard') m (by omega) (by omega)
      · exact subsingleton_HPrime_basicOpen M hn g
      · exact ih _ hcard' (m + 1) hn (by omega)

/-- **Every open of a noetherian affine scheme has a cohomological dimension bound.**  For a
quasicoherent sheaf `M` on `Spec R` and any open `U`, there is an `r` with `Hⁿ(U, M) = 0` for
all `n ≥ max 1 r`; `r` may be taken to be the number of basic opens needed to cover `U`. -/
theorem exists_subsingleton_HPrime (M : (Spec R).Modules) [M.IsQuasicoherent]
    (U : Opens (PrimeSpectrum R)) :
    ∃ r : ℕ, ∀ n : ℕ, 1 ≤ n → r ≤ n →
      Subsingleton (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M).H' n U) := by
  obtain ⟨S, rfl⟩ := exists_finsetOpen U
  exact ⟨S.card, fun n hn hkn =>
    subsingleton_HPrime_finsetOpen M S.card S le_rfl n hn hkn⟩

end AlgebraicGeometry.tilde
