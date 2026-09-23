module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Base change of exterior powers

Supporting API with no Stacks Project counterpart of its own, consumed by the
exterior-power sheaf of §2.2 (the relative Plücker embedding `Gr(q, V) ↪ Gr(1, ⋀^q V)`
of **Theorem 2.1.1**): the canonical isomorphism

`S ⊗[R] ⋀[R]^n M ≃ₗ[S] ⋀[S]^n (S ⊗[R] M)`.

Mathlib (2026-01) has no base change for `exteriorPower`, `ExteriorAlgebra`,
`CliffordAlgebra`, or `MultilinearMap`.  The construction here avoids multilinear
extension of scalars entirely:

* the forward map is the `liftBaseChange` of the `R`-linear map classified by the
  alternating map `m ↦ ιMulti (fun i ↦ 1 ⊗ m i)`;
* surjectivity is the span of `ιMulti` plus multilinear expansion of tuples of
  tensors;
* injectivity comes from an explicit retraction built at the level of exterior
  *algebras*: the algebra homomorphism
  `ExteriorAlgebra S (S ⊗ M) →ₐ[S] S ⊗ ExteriorAlgebra R M` classified by the
  base-changed `ι` (whose values square to zero by the anticommutation of `ι`),
  followed by the base change of the degree-`n` projection of the graded algebra
  structure.

Main declarations:
- `exteriorPower.baseChangeMap`;
- `exteriorPower.algebraBaseChangeHom`;
- `exteriorPower.baseChangeEquiv`.
-/

@[expose] public section

universe u v w

open TensorProduct

namespace exteriorPower

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
variable (n : ℕ) (M : Type w) [AddCommGroup M] [Module R M]

/-- The canonical `R`-alternating map `M^n → ⋀[S]^n (S ⊗[R] M)`, sending a tuple to the
wedge of the associated pure tensors. -/
noncomputable def baseChangeAlternating : M [⋀^Fin n]→ₗ[R] ⋀[S]^n (S ⊗[R] M) :=
  AlternatingMap.compLinearMap
    { toMultilinearMap :=
        (exteriorPower.ιMulti S n (M := S ⊗[R] M)).toMultilinearMap.restrictScalars R
      map_eq_zero_of_eq' := fun v i j hv hij ↦
        (exteriorPower.ιMulti S n (M := S ⊗[R] M)).map_eq_zero_of_eq v hv hij }
    (TensorProduct.mk R S M 1)

@[simp]
lemma baseChangeAlternating_apply (m : Fin n → M) :
    baseChangeAlternating R S n M m =
      exteriorPower.ιMulti S n (fun i ↦ (1 : S) ⊗ₜ[R] m i) := rfl

/-- The classifying `R`-linear map `⋀[R]^n M → ⋀[S]^n (S ⊗[R] M)`. -/
noncomputable def baseChangeAux : ⋀[R]^n M →ₗ[R] ⋀[S]^n (S ⊗[R] M) :=
  exteriorPower.alternatingMapLinearEquiv (baseChangeAlternating R S n M)

@[simp]
lemma baseChangeAux_ιMulti (m : Fin n → M) :
    baseChangeAux R S n M (exteriorPower.ιMulti R n m) =
      exteriorPower.ιMulti S n (fun i ↦ (1 : S) ⊗ₜ[R] m i) := by
  rw [baseChangeAux, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    baseChangeAlternating_apply]

/-- **The base-change comparison map** `S ⊗[R] ⋀[R]^n M →ₗ[S] ⋀[S]^n (S ⊗[R] M)`. -/
noncomputable def baseChangeMap : S ⊗[R] ⋀[R]^n M →ₗ[S] ⋀[S]^n (S ⊗[R] M) :=
  (baseChangeAux R S n M).liftBaseChange S

@[simp]
lemma baseChangeMap_tmul_ιMulti (s : S) (m : Fin n → M) :
    baseChangeMap R S n M (s ⊗ₜ exteriorPower.ιMulti R n m) =
      s • exteriorPower.ιMulti S n (fun i ↦ (1 : S) ⊗ₜ[R] m i) := by
  rw [baseChangeMap, LinearMap.liftBaseChange_tmul, baseChangeAux_ιMulti]

/-- The values of the base-changed `ι` anticommute. -/
lemma baseChange_ι_anticommute (y z : S ⊗[R] M) :
    ((ExteriorAlgebra.ι R (M := M)).baseChange S) y *
        ((ExteriorAlgebra.ι R (M := M)).baseChange S) z +
      ((ExteriorAlgebra.ι R (M := M)).baseChange S) z *
        ((ExteriorAlgebra.ι R (M := M)).baseChange S) y = 0 := by
  induction y with
  | zero => simp
  | tmul s m =>
    induction z with
    | zero => simp
    | tmul t m' =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_comm t s, ← TensorProduct.tmul_add, ExteriorAlgebra.ι_add_mul_swap,
        TensorProduct.tmul_zero]
    | add z₁ z₂ h₁ h₂ =>
      rw [map_add, mul_add, add_mul]
      calc _ = (((ExteriorAlgebra.ι R (M := M)).baseChange S) (s ⊗ₜ m) *
            ((ExteriorAlgebra.ι R (M := M)).baseChange S) z₁ +
          ((ExteriorAlgebra.ι R (M := M)).baseChange S) z₁ *
            ((ExteriorAlgebra.ι R (M := M)).baseChange S) (s ⊗ₜ m)) +
          (((ExteriorAlgebra.ι R (M := M)).baseChange S) (s ⊗ₜ m) *
            ((ExteriorAlgebra.ι R (M := M)).baseChange S) z₂ +
          ((ExteriorAlgebra.ι R (M := M)).baseChange S) z₂ *
            ((ExteriorAlgebra.ι R (M := M)).baseChange S) (s ⊗ₜ m)) := by
            abel
        _ = 0 := by
              rw [h₁, h₂, add_zero]

  | add y₁ y₂ h₁ h₂ =>
    rw [map_add, mul_add, add_mul]
    calc _ = (((ExteriorAlgebra.ι R (M := M)).baseChange S) y₁ *
          ((ExteriorAlgebra.ι R (M := M)).baseChange S) z +
        ((ExteriorAlgebra.ι R (M := M)).baseChange S) z *
          ((ExteriorAlgebra.ι R (M := M)).baseChange S) y₁) +
        (((ExteriorAlgebra.ι R (M := M)).baseChange S) y₂ *
          ((ExteriorAlgebra.ι R (M := M)).baseChange S) z +
        ((ExteriorAlgebra.ι R (M := M)).baseChange S) z *
          ((ExteriorAlgebra.ι R (M := M)).baseChange S) y₂) := by
          abel
      _ = 0 := by
            rw [h₁, h₂, add_zero]


/-- The values of the base-changed `ι` square to zero. -/
lemma baseChange_ι_sq_zero (x : S ⊗[R] M) :
    ((ExteriorAlgebra.ι R (M := M)).baseChange S) x *
      ((ExteriorAlgebra.ι R (M := M)).baseChange S) x = 0 := by
  induction x with
  | zero => simp
  | tmul s m =>
    rw [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul,
      ExteriorAlgebra.ι_sq_zero, TensorProduct.tmul_zero]
  | add a b ha hb =>
    rw [map_add, add_mul, mul_add, mul_add]
    calc _ = (((ExteriorAlgebra.ι R (M := M)).baseChange S) a *
          ((ExteriorAlgebra.ι R (M := M)).baseChange S) a +
        ((ExteriorAlgebra.ι R (M := M)).baseChange S) b *
          ((ExteriorAlgebra.ι R (M := M)).baseChange S) b) +
        (((ExteriorAlgebra.ι R (M := M)).baseChange S) a *
          ((ExteriorAlgebra.ι R (M := M)).baseChange S) b +
        ((ExteriorAlgebra.ι R (M := M)).baseChange S) b *
          ((ExteriorAlgebra.ι R (M := M)).baseChange S) a) := by
          abel
      _ = 0 := by
            rw [ha, hb, baseChange_ι_anticommute]
            simp

/-- The algebra comparison `ExteriorAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] ExteriorAlgebra R M`,
classified by the base change of `ι`. -/
noncomputable def algebraBaseChangeHom :
    ExteriorAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] ExteriorAlgebra R M :=
  ExteriorAlgebra.lift S
    ⟨(ExteriorAlgebra.ι R (M := M)).baseChange S, baseChange_ι_sq_zero R S M⟩

@[simp]
lemma algebraBaseChangeHom_ι (x : S ⊗[R] M) :
    algebraBaseChangeHom R S M (ExteriorAlgebra.ι S x) =
      ((ExteriorAlgebra.ι R (M := M)).baseChange S) x := by
  rw [algebraBaseChangeHom, ExteriorAlgebra.lift_ι_apply]

/-- The degree-`n` projection of the exterior algebra. -/
noncomputable def gradeProj : ExteriorAlgebra R M →ₗ[R] ⋀[R]^n M where
  toFun x := (DirectSum.decompose
    (fun i ↦ (⋀[R]^i M : Submodule R (ExteriorAlgebra R M))) x) n
  map_add' x y := by
    rw [DirectSum.decompose_add, DirectSum.add_apply]
  map_smul' r x := by
    rw [DirectSum.decompose_smul, DirectSum.smul_apply]
    rfl

lemma gradeProj_of_mem {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    gradeProj R n M x = ⟨x, hx⟩ :=
  Subtype.ext (DirectSum.decompose_of_mem_same
    (fun i ↦ (⋀[R]^i M : Submodule R (ExteriorAlgebra R M))) hx)

/-- The retraction `⋀[S]^n (S ⊗[R] M) →ₗ[S] S ⊗[R] ⋀[R]^n M`: include into the exterior
algebra, apply the algebra comparison, and project onto degree `n`. -/
noncomputable def baseChangeRetraction :
    ⋀[S]^n (S ⊗[R] M) →ₗ[S] S ⊗[R] (⋀[R]^n M : Submodule R (ExteriorAlgebra R M)) :=
  ((gradeProj R n M).baseChange S).comp
    ((algebraBaseChangeHom R S M).toLinearMap.comp
      (Submodule.subtype (⋀[S]^n (S ⊗[R] M))))

/-- The product of pure tensors with first factor `1` is the pure tensor of the
product. -/
lemma one_tmul_list_prod {A : Type w} [Ring A] [Algebra R A] (l : List A) :
    (l.map (fun a ↦ ((1 : S) ⊗ₜ[R] a : S ⊗[R] A))).prod = (1 : S) ⊗ₜ[R] l.prod := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, List.prod_nil, Algebra.TensorProduct.one_def]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- The membership of the algebra-level wedge in the `n`-th exterior power. -/
lemma ιMulti_alg_mem (m : Fin n → M) :
    ExteriorAlgebra.ιMulti R n m ∈ ⋀[R]^n M := by
  rw [← exteriorPower.ιMulti_apply_coe]
  exact (exteriorPower.ιMulti R n m).2

/-- The retraction splits the comparison map. -/
lemma baseChangeRetraction_baseChangeMap (x : S ⊗[R] (⋀[R]^n M : Submodule R (ExteriorAlgebra R M))) :
    baseChangeRetraction R S n M (baseChangeMap R S n M x) = x := by
  have key : ∀ w : ⋀[R]^n M,
      baseChangeRetraction R S n M (baseChangeMap R S n M ((1 : S) ⊗ₜ w)) =
        (1 : S) ⊗ₜ w := by
    intro w
    have hw : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
      rw [exteriorPower.ιMulti_span]
      trivial
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨m, rfl⟩ := hw
      rw [baseChangeMap_tmul_ιMulti, one_smul]
      show ((gradeProj R n M).baseChange S)
        ((algebraBaseChangeHom R S M)
          ((exteriorPower.ιMulti S n (fun i ↦ (1 : S) ⊗ₜ[R] m i) :
            ⋀[S]^n (S ⊗[R] M)) : ExteriorAlgebra S (S ⊗[R] M))) =
        (1 : S) ⊗ₜ exteriorPower.ιMulti R n m
      rw [exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply, map_list_prod,
        List.map_ofFn]
      have hfac : (List.ofFn ((algebraBaseChangeHom R S M) ∘
          fun i ↦ ExteriorAlgebra.ι S ((1 : S) ⊗ₜ[R] m i))) =
          List.map (fun a ↦ ((1 : S) ⊗ₜ[R] a : S ⊗[R] ExteriorAlgebra R M))
            (List.ofFn fun i ↦ ExteriorAlgebra.ι R (m i)) := by
        rw [List.map_ofFn]
        refine congrArg List.ofFn (funext fun i ↦ ?_)
        show (algebraBaseChangeHom R S M) (ExteriorAlgebra.ι S ((1 : S) ⊗ₜ[R] m i)) = _
        rw [algebraBaseChangeHom_ι, LinearMap.baseChange_tmul]
        rfl
      rw [hfac, one_tmul_list_prod, ← ExteriorAlgebra.ιMulti_apply,
        LinearMap.baseChange_tmul, gradeProj_of_mem R n M (ιMulti_alg_mem R n M m)]
      exact congrArg (fun w ↦ (1 : S) ⊗ₜ[R] w)
        (Subtype.ext (exteriorPower.ιMulti_apply_coe (R := R) (n := n) (M := M) m).symm)
    | zero =>
      rw [TensorProduct.tmul_zero, map_zero, map_zero]
    | add u v hu hv h1 h2 =>
      rw [TensorProduct.tmul_add, map_add, map_add, h1, h2]
    | smul r u hu h1 =>
      rw [TensorProduct.tmul_smul, LinearMap.map_smul_of_tower,
        LinearMap.map_smul_of_tower, h1]
  induction x with
  | zero => rw [map_zero, map_zero]
  | tmul s w =>
    have h1 : (s ⊗ₜ w : S ⊗[R] (⋀[R]^n M : Submodule R (ExteriorAlgebra R M))) =
        s • ((1 : S) ⊗ₜ w) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, map_smul, key w]
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]

set_option maxHeartbeats 6400000 in
/-- The comparison map is surjective: wedges of tensors expand into images. -/
lemma baseChangeMap_surjective : Function.Surjective (baseChangeMap R S n M) := by
  rw [← LinearMap.range_eq_top, ← top_le_iff, ← exteriorPower.ιMulti_span S n
    (M := S ⊗[R] M), Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  classical
  choose t ht using fun i ↦ TensorProduct.exists_finset (v i)
  have hv : v = fun i ↦ ∑ p ∈ t i, p.1 ⊗ₜ[R] p.2 := funext fun i ↦ ht i
  rw [SetLike.mem_coe, hv]
  rw [show ((exteriorPower.ιMulti S n (M := S ⊗[R] M))
      fun i ↦ ∑ p ∈ t i, p.1 ⊗ₜ[R] p.2) =
      ∑ r ∈ Fintype.piFinset t, (exteriorPower.ιMulti S n (M := S ⊗[R] M))
        (fun i ↦ (r i).1 ⊗ₜ[R] (r i).2) from
    (exteriorPower.ιMulti S n (M := S ⊗[R] M)).toMultilinearMap.map_sum_finset
      (g := fun i p ↦ p.1 ⊗ₜ[R] p.2) (A := t)]
  apply Submodule.sum_mem
  intro r hr
  have hterm : (exteriorPower.ιMulti S n (M := S ⊗[R] M))
      (fun i ↦ (r i).1 ⊗ₜ[R] (r i).2) =
      (∏ i, (r i).1) • (exteriorPower.ιMulti S n (M := S ⊗[R] M))
        (fun i ↦ (1 : S) ⊗ₜ[R] (r i).2) := by
    have hslot : (fun i ↦ ((r i).1 ⊗ₜ[R] (r i).2 : S ⊗[R] M)) =
        fun i ↦ (r i).1 • ((1 : S) ⊗ₜ[R] (r i).2) := by
      refine funext fun i ↦ ?_
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hslot]
    exact (exteriorPower.ιMulti S n (M := S ⊗[R] M)).map_smul_univ _ _
  rw [hterm, ← baseChangeMap_tmul_ιMulti]
  exact LinearMap.mem_range_self _ _

/-- **Base change of exterior powers**:
`S ⊗[R] ⋀[R]^n M ≃ₗ[S] ⋀[S]^n (S ⊗[R] M)`. -/
noncomputable def baseChangeEquiv :
    S ⊗[R] (⋀[R]^n M : Submodule R (ExteriorAlgebra R M)) ≃ₗ[S] ⋀[S]^n (S ⊗[R] M) :=
  LinearEquiv.ofBijective (baseChangeMap R S n M)
    ⟨Function.LeftInverse.injective (g := baseChangeRetraction R S n M)
      (fun x ↦ baseChangeRetraction_baseChangeMap R S n M x),
     baseChangeMap_surjective R S n M⟩

@[simp]
lemma baseChangeEquiv_apply (x : S ⊗[R] (⋀[R]^n M : Submodule R (ExteriorAlgebra R M))) :
    baseChangeEquiv R S n M x = baseChangeMap R S n M x := rfl

/-- The `⋀`-functoriality of a linear equivalence. -/
noncomputable def mapEquiv {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N) :
    (⋀[R]^n M : Submodule R (ExteriorAlgebra R M)) ≃ₗ[R]
      (⋀[R]^n N : Submodule R (ExteriorAlgebra R N)) :=
  LinearEquiv.ofLinear (exteriorPower.map n e.toLinearMap)
    (exteriorPower.map n e.symm.toLinearMap)
    (by
      rw [← exteriorPower.map_comp,
        show e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id from by
          ext x
          simp,
        exteriorPower.map_id])
    (by
      rw [← exteriorPower.map_comp,
        show e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id from by
          ext x
          simp,
        exteriorPower.map_id])

@[simp]
lemma mapEquiv_apply {N : Type*} [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (x : (⋀[R]^n M : Submodule R (ExteriorAlgebra R M))) :
    mapEquiv R n M e x = exteriorPower.map n e.toLinearMap x := rfl

section Semilinear

variable {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] [Module S M₂] [IsScalarTower R S M₂]

/-- The `⋀`-functoriality of a restriction-of-scalars linear map into a module over a
larger ring. -/
noncomputable def mapSemilinear (f : M →ₗ[R] M₂) :
    (⋀[R]^n M : Submodule R (ExteriorAlgebra R M)) →ₗ[R]
      (⋀[S]^n M₂ : Submodule S (ExteriorAlgebra S M₂)) :=
  exteriorPower.alternatingMapLinearEquiv
    (AlternatingMap.compLinearMap
      { toMultilinearMap :=
          (exteriorPower.ιMulti S n (M := M₂)).toMultilinearMap.restrictScalars R
        map_eq_zero_of_eq' := fun v i j hv hij ↦
          (exteriorPower.ιMulti S n (M := M₂)).map_eq_zero_of_eq v hv hij }
      f)

@[simp]
lemma mapSemilinear_ιMulti (f : M →ₗ[R] M₂) (m : Fin n → M) :
    mapSemilinear R S n M f (exteriorPower.ιMulti R n m) =
      exteriorPower.ιMulti S n (fun i ↦ f (m i)) := by
  rw [mapSemilinear, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- **Localization commutes with exterior powers**: if `f` exhibits `M₂` as the
localization of `M` at `S₀` over `R' = S₀⁻¹R`, then the induced map of exterior powers
exhibits `⋀[R']^n M₂` as the localization of `⋀[R]^n M` at `S₀`. -/
theorem isLocalizedModule_mapSemilinear (S₀ : Submonoid R) [IsLocalization S₀ S]
    (f : M →ₗ[R] M₂) [IsLocalizedModule S₀ f] :
    IsLocalizedModule S₀ (mapSemilinear R S n M f) := by
  rw [isLocalizedModule_iff_isBaseChange S₀ S]
  have hbc : IsBaseChange S f := (isLocalizedModule_iff_isBaseChange S₀ S f).mp inferInstance
  refine IsBaseChange.of_equiv
    ((baseChangeEquiv R S n M).trans (mapEquiv S n (S ⊗[R] M) hbc.equiv)) ?_
  -- both sides are additive and `R`-homogeneous in the exterior class; check on wedges
  intro w
  have hw : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R n (M := M))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨m, rfl⟩ := hw
    rw [LinearEquiv.trans_apply, baseChangeEquiv_apply, baseChangeMap_tmul_ιMulti,
      one_smul, mapEquiv_apply, mapSemilinear_ιMulti, exteriorPower.map_apply_ιMulti]
    refine congrArg (exteriorPower.ιMulti S n) (funext fun i ↦ ?_)
    show hbc.equiv ((1 : S) ⊗ₜ[R] m i) = f (m i)
    rw [hbc.equiv_tmul, one_smul]
  | zero =>
    rw [TensorProduct.tmul_zero, map_zero, map_zero]
  | add u v hu hv h1 h2 =>
    rw [TensorProduct.tmul_add, map_add, map_add, h1, h2]
  | smul r u hu h1 =>
    rw [TensorProduct.tmul_smul, ← algebraMap_smul S r, map_smul, map_smul,
      algebraMap_smul, h1]

end Semilinear

section SpanExpansion

variable {R₀ : Type*} [CommRing R₀] {M₀ : Type*} [AddCommGroup M₀] [Module R₀ M₀]

/-- A wedge of elements of a span lies in the span of the wedges of generators. -/
lemma ιMulti_mem_span_of_forall_mem_span (q : ℕ) (S : Set M₀) (m : Fin q → M₀)
    (hm : ∀ i, m i ∈ Submodule.span R₀ S) :
    exteriorPower.ιMulti R₀ q m ∈ Submodule.span R₀
      {w : (⋀[R₀]^q M₀ : Submodule R₀ (ExteriorAlgebra R₀ M₀)) |
        ∃ g : Fin q → M₀, (∀ i, g i ∈ S) ∧ w = exteriorPower.ιMulti R₀ q g} := by
  classical
  have hrep : ∀ i, ∃ (n : ℕ) (c : Fin n → R₀) (g : Fin n → M₀),
      (∀ k, g k ∈ S) ∧ (∑ k, c k • g k) = m i := by
    intro i
    obtain ⟨n, c, gs, hsum⟩ := Submodule.mem_span_set'.mp (hm i)
    exact ⟨n, c, fun k ↦ (gs k : M₀), fun k ↦ (gs k).2, hsum⟩
  choose n c g hgS hsum using hrep
  have hm' : m = fun i ↦ ∑ k : Fin (n i), c i k • g i k :=
    funext fun i ↦ (hsum i).symm
  rw [hm']
  rw [show exteriorPower.ιMulti R₀ q (fun i ↦ ∑ k : Fin (n i), c i k • g i k) =
    (exteriorPower.ιMulti R₀ q).toMultilinearMap
      (fun i ↦ ∑ k : Fin (n i), c i k • g i k) from rfl]
  rw [MultilinearMap.map_sum]
  refine Submodule.sum_mem _ ?_
  intro p _
  rw [MultilinearMap.map_smul_univ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    ⟨fun i ↦ g i (p i), fun i ↦ hgS i (p i), rfl⟩)

end SpanExpansion

section Projective

variable {R n M}

/-- Exterior powers of projective modules are projective: a retract of a free module
passes through the functor, and exterior powers of free modules are free. -/
theorem projective_exteriorPower [Module.Projective R M] :
    Module.Projective R (⋀[R]^n M : Submodule R (ExteriorAlgebra R M)) := by
  obtain ⟨s, hs⟩ := Module.projective_def'.mp ‹Module.Projective R M›
  refine Module.Projective.of_split (exteriorPower.map n s)
    (exteriorPower.map n (Finsupp.linearCombination R id)) ?_
  rw [← exteriorPower.map_comp, hs, exteriorPower.map_id]

/-- The rank of an exterior power of a finite projective module at a point of the
spectrum is the binomial coefficient of the rank. -/
theorem rankAtStalk_exteriorPower [Module.Finite R M] [Module.Projective R M]
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (⋀[R]^n M : Submodule R (ExteriorAlgebra R M)) p =
      (Module.rankAtStalk M p).choose n := by
  classical
  haveI := isLocalizedModule_mapSemilinear (R := R)
    (S := Localization.AtPrime p.asIdeal) (n := n) (M := M)
    p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
  let e := (IsLocalizedModule.iso p.asIdeal.primeCompl
    (mapSemilinear R (Localization.AtPrime p.asIdeal) n M
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M))).extendScalarsOfIsLocalization
    p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
  haveI : Module.Finite (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) :=
    Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
  haveI : Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl M) :=
    Module.free_of_flat_of_isLocalRing
  rw [Module.rankAtStalk, e.finrank_eq, exteriorPower.finrank_eq]
  rfl

end Projective

end exteriorPower

end
