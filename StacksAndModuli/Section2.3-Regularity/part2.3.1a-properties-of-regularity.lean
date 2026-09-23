module

public import StacksAndModuli.«Section2.3-Regularity».«part2.3.1-definition-and-basic-properties»

/-!
# Castelnuovo's properties of regularity

This module continues the first subsection ("Definition and basic properties") of §2.3
(Castelnuovo–Mumford regularity) of Chapter 2 of *Stacks and Moduli*,
label `sec:regularity`. It formalizes Castelnuovo's
**Proposition 2.3.5** (`prop:properties-of-regularity`) and the refinement
**Lemma 2.3.7** (`lem:restriction-surjective`) used in the proof of Theorem 2.3.8.

Everything is stated in the graded-module model of quasi-coherent sheaves on `ℙⁿ_k` relative
to a packaged cohomology theory `C : Cohomology k`; see this folder's COMMENTARY.md. The
hypothesis that `k` be infinite comes from the book's first reduction (flat base change), and
is what makes a hyperplane avoiding the associated points available.

Main book results:
- `Cohomology.isMRegular_of_le_of_field`, `Cohomology.mulSpan_eq_top_of_field`,
  `Cohomology.subsingleton_Hgr_of_le_of_field`,
  `Cohomology.isGloballyGenerated_of_le_of_field`: the three parts of **Proposition
  2.3.5** over an arbitrary base field.
- `Cohomology.surjective_map_toCoker_of_le`: **Lemma 2.3.7**
  (`lem:restriction-surjective`).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

section PropPropertiesOfRegularity

open CategoryTheory AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.ProjectiveSpace.GradedModule

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

variable {k : Type u} [Field k] (C : Cohomology k)

/-- API lemma for Proposition 2.3.5 (part (1)): if the coherent sheaf `F` on
`ℙⁿ` is `m`-regular, then it is `d`-regular for every `d ≥ m`.

The proof is the book's double induction: on `n`, using a hyperplane avoiding the associated
points of `F` and Lemma 2.3.2, and on `d`, using the long exact sequence of
`0 → F(-1) → F → F|_H → 0`. -/
theorem isMRegular_of_le [Infinite k] (n : ℕ) : ∀ M : GradedModule k n, C.IsCoherent M →
    ∀ m d : ℤ, C.IsMRegular M m → m ≤ d → C.IsMRegular M d := by
  induction n with
  | zero =>
      intro M _ m d _ _ i hi
      exact C.subsingleton_of_lt M i (d - i) (by omega)
  | succ n ih =>
      -- the hyperplane is available only for modules with no irrelevant torsion, so prove
      -- the statement there first and transport it along the torsion quotient
      have key : ∀ M : GradedModule k (n + 1), C.IsCoherent M → C.NoIrrelevantTorsion M →
          ∀ m d : ℤ, C.IsMRegular M m → m ≤ d → C.IsMRegular M d := by
        intro M hM htf m d hreg hd
        obtain ⟨c, j, hj, hL, -⟩ :=
          C.exists_nonZeroDivisor_linearForm inferInstance M M hM hM htf htf
        have hSE : ShortExact (M.mulLHom c) (toCoker (M.mulLHom c) : M ⟶ M.quotL c) :=
          shortExact_toCoker _ hL
        have hcoh : C.IsCoherent (M.restrictL c j) := C.isCoherent_restrictL hM c j hj
        have hres : C.IsMRegular (M.restrictL c j) m :=
          C.isMRegular_restrictL hreg c j hj hcoh hL
        have hresle : ∀ e : ℤ, m ≤ e → C.IsMRegular (M.restrictL c j) e :=
          fun e he => ih _ hcoh m e hres he
        induction d, hd using Int.leInduction with
        | base => exact hreg
        | succ e _ hMe =>
          intro i hi
          refine C.subsingleton_H_X₂ hSE i (e + 1 - i) ?_ ?_
          · rw [C.subsingleton_Hgr_twist_iff]
            have heq : e + 1 - (i : ℤ) + -1 = e - i := by ring
            rw [heq]
            exact hMe i hi
          · have hq : Subsingleton ((C.Hgr (M.quotL c) i).obj (e + 1 - (i : ℤ))) := by
              rw [← C.subsingleton_Hgr_restrictL_iff M c j hj hcoh]
              exact hresle (e + 1) (by omega) i hi
            exact hq
      intro M hM m d hreg hd
      obtain ⟨N, φ, hNcoh, hNtf, -, -, hbij⟩ := C.exists_noIrrelevantTorsion_quotient hM
      exact (C.isMRegular_congr φ hbij d).mpr
        (key N hNcoh hNtf m d ((C.isMRegular_congr φ hbij m).mp hreg) hd)

/-- API lemma for Proposition 2.3.5 (part (2)) (the case `k = 1` of the
multiplication map, which the book's induction establishes directly): if `F` is `m`-regular on
`ℙⁿ⁺¹`, `L` is a nonzerodivisor on `F`, `D ≥ m`, and the multiplication maps of `F|_H` already
span in the step from `D` to `D+1`, then so do those of `F`.

This is the restriction diagram in the proof of Proposition 2.3.5: the map `ν_D` is
surjective because `H¹(ℙⁿ⁺¹, F(D-1)) = 0`, and the kernel of `ν_{D+1}` is the image of
multiplication by `L`, which is itself a multiplication map. -/
theorem mulSpan_succ_of_restrict [Infinite k] {n : ℕ} {M : GradedModule k (n + 1)}
    (hM : C.IsCoherent M) {m D : ℤ} (hreg : C.IsMRegular M m) (hD : m ≤ D)
    (c : Fin (n + 2) → k) (j : Fin (n + 2)) (hj : IsUnit (c j))
    (hL : ∀ d, Function.Injective ((M.mulLHom c).app d).hom)
    (hIH : (C.Hgr (M.restrictL c j) 0).mulSpan D (D + 1) = ⊤) :
    (C.Hgr M 0).mulSpan D (D + 1) = ⊤ := by
  have hSE : ShortExact (M.mulLHom c) (toCoker (M.mulLHom c) : M ⟶ M.quotL c) :=
    shortExact_toCoker _ hL
  have hnu : ∀ e : ℤ, m ≤ e →
      Function.Surjective ((C.map (toCoker (M.mulLHom c)) 0).app e).hom := by
    intro e he
    refine C.surjective_map_of_subsingleton hSE 0 e ?_
    rw [C.subsingleton_Hgr_twist_iff]
    have hme : C.IsMRegular M e := C.isMRegular_of_le (n + 1) M hM m e hreg he
    have h1 := hme 1 le_rfl
    have heq : e - ((1 : ℕ) : ℤ) = e + -1 := by push_cast; ring
    rwa [heq] at h1
  have hP : (C.Hgr (M.quotL c) 0).mulSpan D (D + 1) = ⊤ :=
    C.mulSpan_Hgr_restrictL_le M c j hj (C.isCoherent_restrictL hM c j hj) 0 D (D + 1) hIH
  have hker : LinearMap.ker ((C.map (toCoker (M.mulLHom c)) 0).app (D + 1)).hom
      ≤ (C.Hgr M 0).mulSpan D (D + 1) := by
    intro y hy
    rw [(C.exact_map_map hSE 0 (D + 1)).linearMap_ker_eq,
      C.range_map_mulLHom M c 0 (D + 1)] at hy
    rw [range_mulL_eq (C.Hgr M 0) c (D + 1 + -1) D (D + 1) (by ring) (by ring)] at hy
    exact range_mulL_le_mulSpan (C.Hgr M 0) c D (D + 1) (by ring) hy
  refine eq_top_iff.mpr fun y _ => ?_
  have hmap := mulSpan_le_map (C.map (toCoker (M.mulLHom c)) 0) D (D + 1) (hnu D hD)
  have hy : ((C.map (toCoker (M.mulLHom c)) 0).app (D + 1)).hom y
      ∈ Submodule.map (((C.map (toCoker (M.mulLHom c)) 0).app (D + 1)).hom)
        ((C.Hgr M 0).mulSpan D (D + 1)) := hmap (hP ▸ Submodule.mem_top)
  obtain ⟨s, hs, hsy⟩ := hy
  have hdiff : y - s ∈ LinearMap.ker ((C.map (toCoker (M.mulLHom c)) 0).app (D + 1)).hom := by
    rw [LinearMap.mem_ker, map_sub, hsy, sub_self]
  have : y = (y - s) + s := by abel
  rw [this]
  exact Submodule.add_mem _ (hker hdiff) hs

/-- API lemma for Proposition 2.3.5 (part (2)): for an `m`-regular coherent
sheaf `F` on `ℙⁿ`, the multiplication map
`H⁰(ℙⁿ, F(d)) ⊗ H⁰(ℙⁿ, 𝒪(e-d)) → H⁰(ℙⁿ, F(e))` is surjective whenever `m ≤ d ≤ e`.

In the graded-module model surjectivity of that map says exactly that the degree-`e` piece of
the graded module of sections is spanned by the products of monomials of degree `e-d` with the
degree-`d` piece, which is `mulSpan d e = ⊤`. -/
theorem mulSpan_eq_top [Infinite k] (n : ℕ) : ∀ M : GradedModule k n, C.IsCoherent M →
    ∀ m d e : ℤ, C.IsMRegular M m → m ≤ d → d ≤ e → (C.Hgr M 0).mulSpan d e = ⊤ := by
  induction n with
  | zero => intro M _ m d e _ _ hde; exact C.mulSpan_zero M d e hde
  | succ n ih =>
      -- as in `isMRegular_of_le`: prove it for the torsion quotient, then transport
      have key : ∀ M : GradedModule k (n + 1), C.IsCoherent M → C.NoIrrelevantTorsion M →
          ∀ m d e : ℤ, C.IsMRegular M m → m ≤ d → d ≤ e → (C.Hgr M 0).mulSpan d e = ⊤ := by
        intro M hM htf m d e hreg hd hde
        obtain ⟨c, j, hj, hL, -⟩ :=
          C.exists_nonZeroDivisor_linearForm inferInstance M M hM hM htf htf
        have hcoh : C.IsCoherent (M.restrictL c j) := C.isCoherent_restrictL hM c j hj
        have hres : C.IsMRegular (M.restrictL c j) m :=
          C.isMRegular_restrictL hreg c j hj hcoh hL
        have hone : ∀ D : ℤ, m ≤ D → (C.Hgr M 0).mulSpan D (D + 1) = ⊤ := fun D hD =>
          C.mulSpan_succ_of_restrict hM hreg hD c j hj hL
            (ih _ hcoh m D (D + 1) hres hD (by omega))
        induction e, hde using Int.leInduction with
        | base => exact mulSpan_self _ d
        | succ f hf hfe => exact mulSpan_trans _ hfe (hone f (le_trans hd hf))
      intro M hM m d e hreg hd hde
      obtain ⟨N, φ, hNcoh, hNtf, -, -, hbij⟩ := C.exists_noIrrelevantTorsion_quotient hM
      rw [mulSpan_eq_top_iff_of_bijective (C.map φ 0) (hbij 0) d e]
      exact key N hNcoh hNtf m d e ((C.isMRegular_congr φ hbij m).mp hreg) hd hde

/-- API lemma for Proposition 2.3.5 (part (3)) (the vanishing half): for an
`m`-regular coherent sheaf `F` on `ℙⁿ` and `d ≥ m`, `Hⁱ(ℙⁿ, F(d)) = 0` for all `i ≥ 1`. -/
theorem subsingleton_Hgr_of_le [Infinite k] {n : ℕ} {M : GradedModule k n} (hM : C.IsCoherent M)
    {m d : ℤ} (hreg : C.IsMRegular M m) (hd : m ≤ d) (i : ℕ) (hi : 1 ≤ i) :
    Subsingleton ((C.Hgr M i).obj d) := by
  have h := C.isMRegular_of_le n M hM m (d + i) hreg (by omega) i hi
  have heq : d + (i : ℤ) - (i : ℤ) = d := by ring
  rwa [heq] at h

/-- API lemma for Proposition 2.3.5 (part (3)) (the global generation half):
for an `m`-regular coherent sheaf `F` on `ℙⁿ` and `d ≥ m`, the twist `F(d)` is globally
generated. -/
theorem isGloballyGenerated_of_le [Infinite k] {n : ℕ} {M : GradedModule k n}
    (hM : C.IsCoherent M) {m d : ℤ} (hreg : C.IsMRegular M m) (hd : m ≤ d) :
    C.IsGloballyGenerated M d := by
  rw [C.isGloballyGenerated_iff hM d]
  exact ⟨d, fun e he => C.mulSpan_eq_top n M hM m d e hreg hd he⟩

/-- **Proposition 2.3.5** (`prop:properties-of-regularity`, part (1)) over an arbitrary base field:
an `m`-regular coherent sheaf on `ℙⁿ_k` is `d`-regular for every `d ≥ m`, with no hypothesis
on `k`. The reduction to the infinite-field case is flat base change. -/
theorem isMRegular_of_le_of_field {n : ℕ} {M : GradedModule k n} (hM : C.IsCoherent M)
    (hC : C.HasInfiniteBaseChange) {m d : ℤ} (hreg : C.IsMRegular M m) (hd : m ≤ d) :
    C.IsMRegular M d := by
  obtain ⟨K', instK', C', hinf, hbc⟩ := hC
  obtain ⟨bc⟩ := hbc
  intro i hi
  rw [← bc.subsingleton_iff M i (d - i)]
  refine C'.isMRegular_of_le n (bc.obj M) (bc.isCoherent M hM) m d ?_ hd i hi
  intro i' hi'
  rw [bc.subsingleton_iff M i' (m - i')]
  exact hreg i' hi'

/-- **Proposition 2.3.5** (`prop:properties-of-regularity`, part (2)) over an arbitrary base field. -/
theorem mulSpan_eq_top_of_field {n : ℕ} {M : GradedModule k n} (hM : C.IsCoherent M)
    (hC : C.HasInfiniteBaseChange) {m d e : ℤ} (hreg : C.IsMRegular M m) (hd : m ≤ d)
    (hde : d ≤ e) : (C.Hgr M 0).mulSpan d e = ⊤ := by
  obtain ⟨K', instK', C', hinf, hbc⟩ := hC
  obtain ⟨bc⟩ := hbc
  rw [← bc.mulSpan_iff M 0 d e]
  refine C'.mulSpan_eq_top n (bc.obj M) (bc.isCoherent M hM) m d e ?_ hd hde
  intro i' hi'
  rw [bc.subsingleton_iff M i' (m - i')]
  exact hreg i' hi'

/-- **Proposition 2.3.5** (`prop:properties-of-regularity`, part (3)) over an arbitrary base field
(the vanishing half). -/
theorem subsingleton_Hgr_of_le_of_field {n : ℕ} {M : GradedModule k n} (hM : C.IsCoherent M)
    (hC : C.HasInfiniteBaseChange) {m d : ℤ} (hreg : C.IsMRegular M m) (hd : m ≤ d) (i : ℕ)
    (hi : 1 ≤ i) : Subsingleton ((C.Hgr M i).obj d) := by
  have h := C.isMRegular_of_le_of_field hM hC hreg (le_trans hd (by omega : d ≤ d + i)) i hi
  have heq : d + (i : ℤ) - (i : ℤ) = d := by ring
  rwa [heq] at h

/-- **Proposition 2.3.5** (`prop:properties-of-regularity`, part (3)) over an arbitrary base field
(the global generation half). -/
theorem isGloballyGenerated_of_le_of_field {n : ℕ} {M : GradedModule k n} (hM : C.IsCoherent M)
    (hC : C.HasInfiniteBaseChange) {m d : ℤ} (hreg : C.IsMRegular M m) (hd : m ≤ d) :
    C.IsGloballyGenerated M d := by
  rw [C.isGloballyGenerated_iff hM d]
  exact ⟨d, fun e he => C.mulSpan_eq_top_of_field hM hC hreg hd he⟩

end AlgebraicGeometry.ProjectiveSpace.Cohomology

end PropPropertiesOfRegularity

section LemRestrictionSurjective

open CategoryTheory AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.ProjectiveSpace.GradedModule

namespace AlgebraicGeometry.ProjectiveSpace.Cohomology

variable {k : Type u} [Field k] (C : Cohomology k)

/-- API lemma for Lemma 2.3.7 (the remark preceding it): if `F` is
`m`-regular on `ℙⁿ⁺¹` and the linear form `L` is a nonzerodivisor on `F`, then the restriction
map `ν_d : H⁰(ℙⁿ⁺¹, F(d)) → H⁰(H, F|_H(d))` is surjective for every `d ≥ m`.

The book: "`F` is also `d`-regular and the surjectivity follows from the vanishing of
`H¹(ℙⁿ, F(d-1))`". -/
theorem surjective_map_toCoker_of_isMRegular {n : ℕ} {M : GradedModule k (n + 1)}
    (hM : C.IsCoherent M) (hC : C.HasInfiniteBaseChange) (c : Fin (n + 2) → k)
    (hL : ∀ d, Function.Injective ((M.mulLHom c).app d).hom) {m d : ℤ}
    (hreg : C.IsMRegular M m) (hd : m ≤ d) :
    Function.Surjective ((C.map (toCoker (M.mulLHom c)) 0).app d).hom := by
  refine C.surjective_map_of_subsingleton (shortExact_toCoker _ hL) 0 d ?_
  rw [C.subsingleton_Hgr_twist_iff]
  have hme : C.IsMRegular M d := C.isMRegular_of_le_of_field hM hC hreg hd
  have h1 := hme 1 le_rfl
  have heq : d - ((1 : ℕ) : ℤ) = d + -1 := by push_cast; ring
  rwa [heq] at h1

/-- **Lemma 2.3.7** (`lem:restriction-surjective`): let `F` be a coherent sheaf on `ℙⁿ⁺¹` and
`H = V(L)` a hyperplane avoiding the associated points of `F`. If `F|_H` is `m`-regular and the
restriction map `ν_d : H⁰(ℙⁿ⁺¹, F(d)) → H⁰(H, F|_H(d))` is surjective for some `d ≥ m`, then
`ν_p` is surjective for all `p ≥ d`.

Here `ν` is the map induced on `H⁰` by the projection `F → F|_H`; surjectivity of the book's
`ν_p` is surjectivity of this map because the comparison `H⁰(H, F|_H(p)) ≅ H⁰(ℙⁿ⁺¹, (F|_H)(p))`
is an isomorphism. -/
theorem surjective_map_toCoker_of_le [Infinite k] {n : ℕ} {M : GradedModule k (n + 1)}
    (hM : C.IsCoherent M) (c : Fin (n + 2) → k) (j : Fin (n + 2)) (hj : IsUnit (c j))
    {m d : ℤ} (hres : C.IsMRegular (M.restrictL c j) m) (hd : m ≤ d)
    (hsurj : Function.Surjective ((C.map (toCoker (M.mulLHom c)) 0).app d).hom)
    (p : ℤ) (hp : d ≤ p) :
    Function.Surjective ((C.map (toCoker (M.mulLHom c)) 0).app p).hom := by
  induction p, hp using Int.leInduction with
  | base => exact hsurj
  | succ q hq hνq =>
    intro y
    have hq' : m ≤ q := le_trans hd hq
    have h1 : (C.Hgr (M.restrictL c j) 0).mulSpan q (q + 1) = ⊤ :=
      C.mulSpan_eq_top n (M.restrictL c j) (C.isCoherent_restrictL hM c j hj) m q (q + 1)
        hres hq' (by omega)
    have h2 : (C.Hgr (M.quotL c) 0).mulSpan q (q + 1) = ⊤ :=
      C.mulSpan_Hgr_restrictL_le M c j hj (C.isCoherent_restrictL hM c j hj) 0 q (q + 1) h1
    have h3 := mulSpan_le_map (C.map (toCoker (M.mulLHom c)) 0) q (q + 1) hνq
    obtain ⟨z, -, hz⟩ := h3 (h2 ▸ Submodule.mem_top)
    exact ⟨z, hz⟩

end AlgebraicGeometry.ProjectiveSpace.Cohomology

end LemRestrictionSurjective
