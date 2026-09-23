module

public import StacksProject.Algebra.SmoothOverField.«lemma-separable-smooth»
public import StacksAndModuli.API.IdealRegularSequencePrincipalQuotientLift
public import StacksAndModuli.API.ModuleExtDepth

/-!
# Ext-depth of regular local rings

A regular local ring has a regular sequence of maximal possible length: if its Krull
dimension is `d`, its maximal ideal contains a regular sequence of length `d`.  The proof
follows the same quotient induction used for the finite-global-dimension theorem.  In
positive dimension, choose `x` in the maximal ideal but outside its square.  The quotient
by `x` is again regular local of dimension one less, and a regular sequence in its maximal
ideal lifts termwise and can be prefixed by `x`.

Rees's theorem then identifies the existence of this regular sequence with Ext-depth at
least `d` along the maximal ideal.  This is the maximal-ideal Cohen--Macaulay input available
without introducing a separate depth-valued invariant.

Main declarations:

* `IsRegularLocalRing.exists_isRegular_maximalIdeal_of_ringKrullDim`;
* `IsRegularLocalRing.extDepthAtLeast_maximalIdeal_of_ringKrullDim`;
* `IsRegularLocalRing.isRegular_of_span_range_eq_maximalIdeal_of_ringKrullDim`;
* `IsRegularLocalRing.isRegular_of_linearIndependent_toCotangent`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open IsLocalRing

namespace IsRegularLocalRing

/-- A regular local ring of Krull dimension `d` has a regular sequence of length `d`
contained in its maximal ideal. -/
theorem exists_isRegular_maximalIdeal_of_ringKrullDim
    (R : Type u) [CommRing R] [IsRegularLocalRing R] {d : ℕ}
    (hdim : ringKrullDim R = (d : WithBot ℕ∞)) :
    ∃ f : Fin d → R, (∀ i, f i ∈ maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular R (List.ofFn f) := by
  induction d generalizing R with
  | zero =>
      refine ⟨Fin.elim0, ?_, ?_⟩
      · exact fun i ↦ Fin.elim0 i
      · simpa using RingTheory.Sequence.IsRegular.nil R R
  | succ d ih =>
      obtain ⟨x, hxm, hxm2, -⟩ :=
        IsLocalRing.exists_mem_maximalIdeal_notMem_pow_two_notMem_minimalPrimes hdim
      have hspan : Ideal.span {x} ≠ (⊤ : Ideal R) :=
        Ideal.span_singleton_ne_top (mem_nonunits_iff.mp hxm)
      let _ : Nontrivial (R ⧸ Ideal.span {x}) :=
        Ideal.Quotient.nontrivial_iff.mpr hspan
      let _ : IsLocalRing (R ⧸ Ideal.span {x}) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _)
          Ideal.Quotient.mk_surjective
      obtain ⟨hregQ, hdimQ⟩ :=
        IsRegularLocalRing.quotient_of_notMem_pow_two hdim x hxm hxm2
      let _ : IsRegularLocalRing (R ⧸ Ideal.span {x}) := hregQ
      obtain ⟨g, hgmem, hgreg⟩ := ih (R ⧸ Ideal.span {x}) hdimQ
      let _ : IsDomain R := IsRegularLocalRing.isDomain
      have hx0 : x ≠ 0 := by
        intro hx
        exact hxm2 (hx ▸ Submodule.zero_mem _)
      have hxreg : IsRegular x := IsRegular.of_ne_zero hx0
      apply Ideal.exists_family_mem_and_isRegular_succ_of_isRegular_map_quotient
        (maximalIdeal R) x hxm hxreg g
      · intro i
        rw [IsLocalRing.map_maximalIdeal_of_surjective
          (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective]
        exact hgmem i
      · exact hgreg

/-- A regular local ring of Krull dimension `d` has Ext-depth at least `d` along its
maximal ideal. -/
theorem extDepthAtLeast_maximalIdeal_of_ringKrullDim
    (R : Type u) [CommRing R] [IsRegularLocalRing R] {d : ℕ}
    (hdim : ringKrullDim R = (d : WithBot ℕ∞)) :
    ModuleCat.ExtDepthAtLeast (maximalIdeal R) (ModuleCat.of R R) d := by
  have hsmul : maximalIdeal R •
      (⊤ : Submodule R (ModuleCat.of R R)) < ⊤ := by
    rw [← IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact Submodule.jacobson_smul_lt_top _
  apply (ModuleCat.extDepthAtLeast_iff_exists_isRegular
    (maximalIdeal R) (ModuleCat.of R R) d hsmul).mpr
  obtain ⟨f, hfmem, hfreg⟩ :=
    exists_isRegular_maximalIdeal_of_ringKrullDim R hdim
  refine ⟨List.ofFn f, by simp, ?_, hfreg⟩
  intro r hr
  rw [List.mem_ofFn'] at hr
  obtain ⟨i, rfl⟩ := hr
  exact hfmem i

/-- A generating family of the maximal ideal of a regular local ring is a regular
sequence when its cardinality is the Krull dimension. -/
theorem isRegular_of_span_range_eq_maximalIdeal_of_ringKrullDim
    (R : Type u) [CommRing R] [IsRegularLocalRing R] {d : ℕ}
    (hdim : ringKrullDim R = (d : WithBot ℕ∞))
    (f : Fin d → maximalIdeal R)
    (hspan : Ideal.span (Set.range fun i ↦ (f i : R)) = maximalIdeal R) :
    RingTheory.Sequence.IsRegular R (List.ofFn fun i ↦ (f i : R)) := by
  induction d generalizing R with
  | zero =>
      simpa using RingTheory.Sequence.IsRegular.nil R R
  | succ d ih =>
      have htop : Submodule.span R (Set.range f) = ⊤ := by
        apply (Submodule.map_injective_of_injective
          (maximalIdeal R).subtype_injective)
        rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
          ← Set.range_comp]
        exact hspan
      have hclasses : Submodule.span (ResidueField R)
          (Set.range fun i ↦ (maximalIdeal R).toCotangent (f i)) = ⊤ := by
        rw [Set.range_comp', CotangentSpace.span_image_eq_top_iff]
        exact htop
      have hfinrank : Module.finrank (ResidueField R) (CotangentSpace R) = d + 1 := by
        have h := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
        rw [hdim] at h
        exact_mod_cast h
      have hlin : LinearIndependent (ResidueField R)
          (fun i ↦ (maximalIdeal R).toCotangent (f i)) :=
        linearIndependent_of_top_le_span_of_card_eq_finrank hclasses.ge (by
          simp [hfinrank])
      have hxm : (f 0 : R) ∈ maximalIdeal R := (f 0).2
      have hxm2 : (f 0 : R) ∉ maximalIdeal R ^ 2 := by
        intro hzero
        exact hlin.ne_zero 0 ((Ideal.toCotangent_eq_zero _ _).mpr hzero)
      have hprincipal : Ideal.span {(f 0 : R)} ≠ (⊤ : Ideal R) :=
        Ideal.span_singleton_ne_top (mem_nonunits_iff.mp hxm)
      let _ : Nontrivial (R ⧸ Ideal.span {(f 0 : R)}) :=
        Ideal.Quotient.nontrivial_iff.mpr hprincipal
      let _ : IsLocalRing (R ⧸ Ideal.span {(f 0 : R)}) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _)
          Ideal.Quotient.mk_surjective
      obtain ⟨hregQ, hdimQ⟩ :=
        IsRegularLocalRing.quotient_of_notMem_pow_two hdim (f 0 : R) hxm hxm2
      let _ : IsRegularLocalRing (R ⧸ Ideal.span {(f 0 : R)}) := hregQ
      let q : R →+* R ⧸ Ideal.span {(f 0 : R)} :=
        Ideal.Quotient.mk _
      let g : Fin d → maximalIdeal (R ⧸ Ideal.span {(f 0 : R)}) := fun i ↦
        ⟨q (f i.succ : R), by
          rw [← IsLocalRing.map_maximalIdeal_of_surjective q
            Ideal.Quotient.mk_surjective]
          exact Ideal.mem_map_of_mem q (f i.succ).2⟩
      have hrange : Set.range (fun i : Fin (d + 1) ↦ (f i : R)) =
          insert (f 0 : R) (Set.range fun i : Fin d ↦ (f i.succ : R)) := by
        exact Fin.range_fin_succ fun i ↦ (f i : R)
      have hqzero : q (f 0 : R) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (Ideal.subset_span (Set.mem_singleton (f 0 : R)))
      have hspanQ : Ideal.span (Set.range fun i ↦ (g i :
          R ⧸ Ideal.span {(f 0 : R)})) =
          maximalIdeal (R ⧸ Ideal.span {(f 0 : R)}) := by
        change Ideal.span (Set.range fun i : Fin d ↦ q (f i.succ : R)) = _
        calc
          _ = Ideal.map q
              (Ideal.span (Set.range fun i : Fin (d + 1) ↦ (f i : R))) := by
            rw [Ideal.map_span, hrange, Set.image_insert_eq, hqzero,
              Ideal.span_insert_zero, ← Set.range_comp]
            rfl
          _ = Ideal.map q (maximalIdeal R) := congrArg (Ideal.map q) hspan
          _ = maximalIdeal (R ⧸ Ideal.span {(f 0 : R)}) :=
            IsLocalRing.map_maximalIdeal_of_surjective q
              Ideal.Quotient.mk_surjective
      have htail := ih (R ⧸ Ideal.span {(f 0 : R)}) hdimQ g hspanQ
      have hmap :
          (List.ofFn fun i : Fin d ↦ (f i.succ : R)).map q =
            List.ofFn fun i ↦ (g i : R ⧸ Ideal.span {(f 0 : R)}) := by
        rw [List.map_ofFn]
        rfl
      let eR : QuotSMulTop (f 0 : R) R ≃ₗ[R]
          R ⧸ Ideal.span {(f 0 : R)} :=
        QuotSMulTop.equivQuotTensor (f 0 : R) R ≪≫ₗ
          TensorProduct.rid R (R ⧸ Ideal.span {(f 0 : R)})
      let e : QuotSMulTop (f 0 : R) R ≃ₗ[R ⧸ Ideal.span {(f 0 : R)}]
          R ⧸ Ideal.span {(f 0 : R)} :=
        eR.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
      have htailQuot : RingTheory.Sequence.IsRegular
          (QuotSMulTop (f 0 : R) R)
          ((List.ofFn fun i : Fin d ↦ (f i.succ : R)).map q) := by
        apply (e.isRegular_congr _).mpr
        rw [hmap]
        exact htail
      let _ : IsDomain R := IsRegularLocalRing.isDomain
      have hxzero : (f 0 : R) ≠ 0 := by
        intro hx
        exact hxm2 (hx ▸ Submodule.zero_mem _)
      have hcons : RingTheory.Sequence.IsRegular R
          ((f 0 : R) :: List.ofFn fun i : Fin d ↦ (f i.succ : R)) :=
        (RingTheory.Sequence.isRegular_cons_iff' R (f 0 : R)
          (List.ofFn fun i : Fin d ↦ (f i.succ : R))).mpr
          ⟨(IsRegular.of_ne_zero hxzero).isSMulRegular, htailQuot⟩
      simpa only [List.ofFn_succ] using hcons

/-- A finite family in the maximal ideal of a regular local ring is a regular sequence
when its cotangent classes are linearly independent. -/
theorem isRegular_of_linearIndependent_toCotangent
    (R : Type u) [CommRing R] [IsRegularLocalRing R] {c : ℕ}
    (f : Fin c → maximalIdeal R)
    (hlin : LinearIndependent (ResidueField R)
      fun i ↦ (maximalIdeal R).toCotangent (f i)) :
    RingTheory.Sequence.IsRegular R (List.ofFn fun i ↦ (f i : R)) := by
  let e := Module.finrank (ResidueField R) (CotangentSpace R)
  have hdim : ringKrullDim R = (e : WithBot ℕ∞) :=
    ((IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance).symm
  have hce : c ≤ e := by
    have hspanrank : Module.finrank (ResidueField R)
        (Submodule.span (ResidueField R)
          (Set.range fun i ↦ (maximalIdeal R).toCotangent (f i))) = c := by
      rw [finrank_span_eq_card hlin, Fintype.card_fin]
    have hle := (Submodule.span (ResidueField R)
      (Set.range fun i ↦ (maximalIdeal R).toCotangent (f i))).finrank_le
    rwa [hspanrank] at hle
  let w := e - c
  have hdim' : ringKrullDim R = ((c + w : ℕ) : WithBot ℕ∞) := by
    rw [hdim]
    congr 1
    exact (Nat.add_sub_of_le hce).symm
  obtain ⟨x, hxspan, hxagree⟩ :=
    IsRegularLocalRing.exists_maximalIdeal_generators_append hdim' f hlin
  have hxreg :=
    isRegular_of_span_range_eq_maximalIdeal_of_ringKrullDim R hdim' x hxspan
  let t : Fin w → R := fun i ↦ (x (Fin.natAdd c i) : R)
  have hx : (fun i : Fin (c + w) ↦ (x i : R)) =
      Fin.append (fun i : Fin c ↦ (f i : R)) t := by
    funext i
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · rw [Fin.append_left]
      exact congrArg Subtype.val (hxagree j)
    · rw [Fin.append_right]
  have hfull : RingTheory.Sequence.IsWeaklyRegular R
      (List.ofFn (fun i : Fin c ↦ (f i : R)) ++ List.ofFn t) := by
    rw [← List.ofFn_fin_append, ← hx]
    exact hxreg.toIsWeaklyRegular
  have hprefix : RingTheory.Sequence.IsWeaklyRegular R
      (List.ofFn fun i : Fin c ↦ (f i : R)) :=
    ((RingTheory.Sequence.isWeaklyRegular_append_iff R _ _).mp hfull).1
  apply RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal
  · intro r hr
    rw [List.mem_ofFn'] at hr
    obtain ⟨i, rfl⟩ := hr
    exact (f i).2
  · exact hprefix

end IsRegularLocalRing

end
