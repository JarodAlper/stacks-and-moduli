module

public import StacksAndModuli.API.SimplicialCoeffHomotopy
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

/-!
# The Čech coefficient system of a family of elements of a ring

Supporting API with no Stacks Project counterpart.

For a family `f : ι → R` and an `R`-module `M`, the Čech complex of the corresponding cover of
`Spec R` by the distinguished opens `D(f i)` has, at a finite subset `S ⊆ ι`, the group
`M[1/f_S]` — here modelled as `LocalizedModule (Submonoid.closure (f '' S)) M`, which makes the
restriction maps `M[1/f_S] → M[1/f_T]` for `S ⊆ T` immediate from the universal property.

That data is a `Finset.CoeffSystem` (`API/SimplicialCoeffHomotopy.lean`), and when some `f v` is
**invertible in `R`** it carries a `Retraction` in the direction `v`: inverting a unit changes
nothing, so `M[1/f_{S ∪ {v}}] ≅ M[1/f_S]`, naturally in `S`. The contracting homotopy of that
file then shows the Čech complex is exact — which is the computation on a single chart `D(f_v)`
in the proof that Čech cohomology of a quasi-coherent sheaf on an affine vanishes.

Main declarations:
- `LocalizedModule.cechCoeffSystem`;
- `LocalizedModule.cechRetraction`, for a vertex whose element is a unit.
-/

@[expose] public section

universe u v

namespace LocalizedModule

open Finset Submonoid

variable {ι : Type u} [LinearOrder ι] {R : Type v} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] (f : ι → R) {v : ι}

/-- The multiplicative set inverted at a finite subset of the index. -/
def cechMonoid (S : Finset ι) : Submonoid R := Submonoid.closure (f '' (S : Set ι))

/-- The Čech group at a finite subset: `M` with the `f i`, `i ∈ S`, inverted. -/
abbrev cechObj (S : Finset ι) : Type v := LocalizedModule (cechMonoid f S) M

lemma mem_cechMonoid {S : Finset ι} {i : ι} (hi : i ∈ S) : f i ∈ cechMonoid f S :=
  Submonoid.subset_closure ⟨i, by exact_mod_cast hi, rfl⟩

lemma prod_mem_cechMonoid (S : Finset ι) : (∏ i ∈ S, f i) ∈ cechMonoid f S :=
  Submonoid.prod_mem _ fun _ hi => mem_cechMonoid f hi

lemma cechMonoid_mono {S T : Finset ι} (h : S ⊆ T) : cechMonoid f S ≤ cechMonoid f T :=
  Submonoid.closure_mono (Set.image_mono (by exact_mod_cast h))

/-- Every element inverted at `S` acts invertibly on the Čech group at any larger `T`. -/
lemma isUnit_algebraMap_of_subset {S T : Finset ι} (h : S ⊆ T) (x : cechMonoid f S) :
    IsUnit ((algebraMap R (Module.End R (cechObj f (M := M) T))) (x : R)) :=
  IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (cechMonoid f T) M)
    ⟨(x : R), cechMonoid_mono f h x.2⟩

/-- Restriction of Čech groups along an inclusion of index subsets. -/
noncomputable def cechMap {S T : Finset ι} (h : S ⊆ T) :
    cechObj f (M := M) S →ₗ[R] cechObj f (M := M) T :=
  LocalizedModule.lift _ (LocalizedModule.mkLinearMap (cechMonoid f T) M)
    (isUnit_algebraMap_of_subset f h)

lemma cechMap_mk_one {S T : Finset ι} (h : S ⊆ T) (m : M) :
    cechMap f (M := M) h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  rw [cechMap, LocalizedModule.lift_mk_one]
  rfl

/-- **The Čech coefficient system of a family of ring elements.** -/
noncomputable def cechCoeffSystem :
    Finset.CoeffSystem R (fun S : Finset ι => cechObj f (M := M) S) where
  map h := cechMap f h
  map_self h x := by
    have := LocalizedModule.lift_unique (cechMonoid f _)
      (LocalizedModule.mkLinearMap (cechMonoid f _) M)
      (isUnit_algebraMap_of_subset f h) LinearMap.id (by ext m; rfl)
    exact congrArg (fun g : _ →ₗ[R] _ => g x) this
  map_map h₁ h₂ x := by
    have := LocalizedModule.lift_unique (cechMonoid f _)
      (LocalizedModule.mkLinearMap (cechMonoid f _) M)
      (isUnit_algebraMap_of_subset f (h₁.trans h₂))
      ((cechMap f h₂).comp (cechMap f h₁)) (by
        ext m
        simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
        rw [cechMap_mk_one, cechMap_mk_one])
    exact (congrArg (fun g : _ →ₗ[R] _ => g x) this).symm

lemma cechMap_cechMap {S T U : Finset ι} (h₁ : S ⊆ T) (h₂ : T ⊆ U)
    (x : cechObj f (M := M) S) :
    cechMap f h₂ (cechMap f h₁ x) = cechMap f (h₁.trans h₂) x :=
  (cechCoeffSystem (M := M) f).map_map h₁ h₂ x

@[simp] lemma cechCoeffSystem_map {S T : Finset ι} (h : S ⊆ T) :
    (cechCoeffSystem (M := M) f).map h = cechMap f h := rfl

/-! ## Comparison with localization at the product -/

/-- A divisor of an element acting invertibly acts invertibly. -/
lemma isUnit_algebraMap_of_mul {N : Type v} [AddCommGroup N] [Module R N] {a b : R}
    (h : IsUnit ((algebraMap R (Module.End R N)) (a * b))) :
    IsUnit ((algebraMap R (Module.End R N)) a) := by
  rw [Module.End.isUnit_iff] at h ⊢
  refine ⟨fun x y hxy => h.1 ?_, fun y => ?_⟩
  · show (a * b) • x = (a * b) • y
    rw [mul_comm, mul_smul, mul_smul]
    exact congrArg (b • ·) hxy
  · obtain ⟨x, hx⟩ := h.2 y
    exact ⟨b • x, by rw [← hx]; show a • b • x = (a * b) • x; rw [mul_smul]⟩

/-- Every element of the Čech monoid at `S` divides a power of `∏ i ∈ S, f i`, so it acts
invertibly wherever that product does. -/
lemma isUnit_algebraMap_of_prod {N : Type v} [AddCommGroup N] [Module R N]
    (S : Finset ι) (hprod : IsUnit ((algebraMap R (Module.End R N)) (∏ i ∈ S, f i)))
    {x : R} (hx : x ∈ cechMonoid f S) :
    IsUnit ((algebraMap R (Module.End R N)) x) := by
  classical
  refine Submonoid.closure_induction
    (motive := fun y _ => IsUnit ((algebraMap R (Module.End R N)) y)) ?_ ?_ ?_ hx
  · rintro _ ⟨i, hi, rfl⟩
    have hiS : i ∈ S := by exact_mod_cast hi
    obtain ⟨c, hc⟩ : ∃ c, (∏ j ∈ S, f j) = f i * c :=
      ⟨∏ j ∈ S.erase i, f j, (Finset.mul_prod_erase S f hiS).symm⟩
    exact isUnit_algebraMap_of_mul (by rw [← hc]; exact hprod)
  · rw [map_one]; exact isUnit_one
  · intro a b _ _ ha hb
    rw [map_mul]
    exact ha.mul hb

/-- **Inverting the elements of `S` one at a time is the same as inverting their product.**
This is the bridge to Mathlib's `IsLocalizedModule.Away` instance for the sections of `M~` on a
basic open (`Mathlib/AlgebraicGeometry/Modules/Tilde.lean`), which is stated for
`Submonoid.powers`. -/
lemma isLocalizedModule_cechMonoid_of_powers {N : Type v} [AddCommGroup N] [Module R N]
    (S : Finset ι) (g : M →ₗ[R] N)
    [IsLocalizedModule (Submonoid.powers (∏ i ∈ S, f i)) g] :
    IsLocalizedModule (cechMonoid f S) g where
  map_units x := by
    refine isUnit_algebraMap_of_prod f S ?_ x.2
    exact IsLocalizedModule.map_units g ⟨_, Submonoid.mem_powers (∏ i ∈ S, f i)⟩
  surj y := by
    obtain ⟨⟨m, ⟨t, a, ha⟩⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers (∏ i ∈ S, f i)) g y
    refine ⟨⟨m, ⟨t, ?_⟩⟩, hm⟩
    rw [← ha]
    exact pow_mem (prod_mem_cechMonoid f S) a
  exists_of_eq {x₁ x₂} h := by
    obtain ⟨⟨c, a, ha⟩, hc⟩ :=
      IsLocalizedModule.exists_of_eq (S := Submonoid.powers (∏ i ∈ S, f i)) (f := g) h
    refine ⟨⟨c, ?_⟩, hc⟩
    rw [← ha]
    exact pow_mem (prod_mem_cechMonoid f S) a

/-! ## The retraction at a vertex whose element is a unit -/

variable {f}

/-- If `f v` is a unit in `R`, inverting it as well changes nothing: every element of the
Čech monoid at `insert v S` already acts invertibly on the Čech group at `S`. -/
lemma isUnit_algebraMap_insert (hv : IsUnit (f v)) (S : Finset ι)
    (x : cechMonoid f (insert v S)) :
    IsUnit ((algebraMap R (Module.End R (cechObj f (M := M) S))) (x : R)) := by
  obtain ⟨x, hx⟩ := x
  refine Submonoid.closure_induction (motive := fun y _ =>
    IsUnit ((algebraMap R (Module.End R (cechObj f (M := M) S))) y)) ?_ ?_ ?_ hx
  · rintro _ ⟨i, hi, rfl⟩
    rcases Finset.mem_insert.mp (by exact_mod_cast hi) with rfl | hiS
    · exact hv.map _
    · exact isUnit_algebraMap_of_subset f (le_refl S)
        ⟨f i, Submonoid.subset_closure ⟨i, by exact_mod_cast hiS, rfl⟩⟩
  · rw [map_one]; exact isUnit_one
  · intro a b _ _ ha hb
    rw [map_mul]
    exact ha.mul hb

/-- The retraction `M[1/f_{S ∪ {v}}] → M[1/f_S]` available when `f v` is a unit. -/
noncomputable def cechInv (hv : IsUnit (f v)) (S : Finset ι) :
    cechObj f (M := M) (insert v S) →ₗ[R] cechObj f (M := M) S :=
  LocalizedModule.lift _ (LocalizedModule.mkLinearMap (cechMonoid f S) M)
    (isUnit_algebraMap_insert hv S)

lemma cechInv_mk (hv : IsUnit (f v)) (S : Finset ι) (m : M) :
    cechInv (M := M) hv S (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  rw [cechInv, LocalizedModule.lift_mk_one]
  rfl

/-- **The Čech coefficient system is constant in the direction of a vertex whose element is a
unit.** -/
noncomputable def cechRetraction (hv : IsUnit (f v)) :
    (cechCoeffSystem (M := M) f).Retraction v where
  inv S := cechInv hv S
  inv_map S x := by
    have := LocalizedModule.lift_unique (cechMonoid f S)
      (LocalizedModule.mkLinearMap (cechMonoid f S) M)
      (isUnit_algebraMap_of_subset f (le_refl S))
      ((cechInv hv S).comp (cechMap f (subset_insert v S))) (by
        ext m
        simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
        rw [cechMap_mk_one, cechInv_mk])
    have h2 := congrArg (fun g : _ →ₗ[R] _ => g x) this
    rw [LinearMap.comp_apply] at h2
    rw [cechCoeffSystem_map, ← h2]
    exact (cechCoeffSystem (M := M) f).map_self (le_refl S) x
  map_inv S x := by
    have := LocalizedModule.lift_unique (cechMonoid f (insert v S))
      (LocalizedModule.mkLinearMap (cechMonoid f (insert v S)) M)
      (isUnit_algebraMap_of_subset f (le_refl (insert v S)))
      ((cechMap f (subset_insert v S)).comp (cechInv hv S)) (by
        ext m
        simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
        rw [cechInv_mk, cechMap_mk_one])
    have h2 := congrArg (fun g : _ →ₗ[R] _ => g x) this
    rw [LinearMap.comp_apply] at h2
    rw [cechCoeffSystem_map, ← h2]
    exact (cechCoeffSystem (M := M) f).map_self (le_refl (insert v S)) x
  inv_naturality {S T} h x := by
    have := LocalizedModule.lift_unique (cechMonoid f (insert v S))
      (LocalizedModule.mkLinearMap (cechMonoid f T) M)
      (fun y => isUnit_algebraMap_insert hv T
        ⟨(y : R), cechMonoid_mono f (insert_subset_insert v h) y.2⟩)
      ((cechInv hv T).comp (cechMap f (insert_subset_insert v h))) (by
        ext m
        simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
        rw [cechMap_mk_one, cechInv_mk])
    have this2 := LocalizedModule.lift_unique (cechMonoid f (insert v S))
      (LocalizedModule.mkLinearMap (cechMonoid f T) M)
      (fun y => isUnit_algebraMap_insert hv T
        ⟨(y : R), cechMonoid_mono f (insert_subset_insert v h) y.2⟩)
      ((cechMap f h).comp (cechInv hv S)) (by
        ext m
        simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
        rw [cechInv_mk, cechMap_mk_one])
    have h3 := this.symm.trans this2
    rw [cechCoeffSystem_map, cechCoeffSystem_map]
    exact congrArg (fun g : _ →ₗ[R] _ => g x) h3

/-! ## Adjoining one index is a localization -/

variable (f)

/-- Every element inverted at `insert k S` is a power of `f k` times an element inverted at
`S`. -/
lemma exists_pow_mul_mem_cechMonoid (k : ι) (S : Finset ι) {t : R}
    (ht : t ∈ cechMonoid f (insert k S)) :
    ∃ (a : ℕ) (t' : R), t' ∈ cechMonoid f S ∧ t = (f k) ^ a * t' := by
  refine Submonoid.closure_induction
    (motive := fun y _ => ∃ (a : ℕ) (t' : R), t' ∈ cechMonoid f S ∧ y = (f k) ^ a * t')
    ?_ ?_ ?_ ht
  · rintro _ ⟨i, hi, rfl⟩
    rcases Finset.mem_insert.mp (by exact_mod_cast hi) with rfl | hiS
    · exact ⟨1, 1, one_mem _, by rw [pow_one, mul_one]⟩
    · exact ⟨0, f i, Submonoid.subset_closure ⟨i, by exact_mod_cast hiS, rfl⟩,
        by rw [pow_zero, one_mul]⟩
  · exact ⟨0, 1, one_mem _, by rw [pow_zero, one_mul]⟩
  · rintro a b _ _ ⟨p, a', ha', rfl⟩ ⟨q, b', hb', rfl⟩
    exact ⟨p + q, a' * b', mul_mem ha' hb', by rw [pow_add]; ring⟩

lemma cechMap_mk {S T : Finset ι} (h : S ⊆ T) (m : M) (t : cechMonoid f S) :
    cechMap f (M := M) h (LocalizedModule.mk m t)
      = LocalizedModule.mk m ⟨(t : R), cechMonoid_mono f h t.2⟩ := by
  rw [cechMap, LocalizedModule.lift_mk, Module.End.algebraMap_isUnit_inv_apply_eq_iff,
    LocalizedModule.mkLinearMap_apply, LocalizedModule.smul'_mk]
  exact LocalizedModule.mk_eq.mpr ⟨1, by simp⟩

/-- **Adjoining one index to the Čech group is localization at that element.** -/
instance isLocalizedModule_cechMap_insert (k : ι) (S : Finset ι) :
    IsLocalizedModule (Submonoid.powers (f k))
      (cechMap f (M := M) (Finset.subset_insert k S)) where
  map_units x := by
    refine isUnit_algebraMap_of_subset f (le_refl (insert k S)) ⟨(x : R), ?_⟩
    obtain ⟨a, ha⟩ := x.2
    rw [← ha]
    refine pow_mem (Submonoid.subset_closure ?_) a
    exact ⟨k, by simp, rfl⟩
  surj y := by
    induction y using LocalizedModule.induction_on with
    | _ m t =>
      obtain ⟨a, t', ht', hta⟩ := exists_pow_mul_mem_cechMonoid f k S t.2
      refine ⟨⟨LocalizedModule.mk m ⟨t', ht'⟩, ⟨(f k) ^ a, a, rfl⟩⟩, ?_⟩
      rw [cechMap_mk, Submonoid.smul_def, LocalizedModule.smul'_mk]
      refine LocalizedModule.mk_eq.mpr ⟨1, ?_⟩
      simp only [one_smul, Submonoid.smul_def]
      rw [hta, ← smul_assoc, smul_eq_mul, mul_comm]
  exists_of_eq {x₁ x₂} h := by
    induction x₁ using LocalizedModule.induction_on with
    | _ m₁ t₁ =>
      induction x₂ using LocalizedModule.induction_on with
      | _ m₂ t₂ =>
        rw [cechMap_mk, cechMap_mk] at h
        obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.mp h
        obtain ⟨a, u', hu', hua⟩ := exists_pow_mul_mem_cechMonoid f k S u.2
        refine ⟨⟨(f k) ^ a, a, rfl⟩, ?_⟩
        rw [Submonoid.smul_def, Submonoid.smul_def, LocalizedModule.smul'_mk,
          LocalizedModule.smul'_mk]
        refine LocalizedModule.mk_eq.mpr ⟨⟨u', hu'⟩, ?_⟩
        simp only [Submonoid.smul_def] at hu ⊢
        rw [hua] at hu
        simp only [smul_smul, mul_comm, mul_left_comm, mul_assoc] at hu ⊢
        exact hu

variable {f}

/-! ## The system with one index always inverted -/

variable (f)

/-- The Čech coefficient system with the index `k` always adjoined: `S ↦ M[1/f_{S ∪ {k}}]`.
This is what the Čech system becomes after localizing at `f k`. -/
noncomputable def cechShiftCoeffSystem (k : ι) :
    Finset.CoeffSystem R (fun S : Finset ι => cechObj f (M := M) (insert k S)) where
  map h := cechMap f (Finset.insert_subset_insert k h)
  map_self h x :=
    (cechCoeffSystem (M := M) f).map_self (Finset.insert_subset_insert k h) x
  map_map h₁ h₂ x :=
    (cechCoeffSystem (M := M) f).map_map (Finset.insert_subset_insert k h₁)
      (Finset.insert_subset_insert k h₂) x

@[simp] lemma cechShiftCoeffSystem_map (k : ι) {S T : Finset ι} (h : S ⊆ T) :
    (cechShiftCoeffSystem (M := M) f k).map h
      = cechMap f (Finset.insert_subset_insert k h) := rfl

/-- **The shifted system is constant in the direction of `k`**, because `insert k` is
idempotent. No hypothesis on `f k` is needed: the index is already there. -/
noncomputable def cechShiftRetraction (k : ι) :
    (cechShiftCoeffSystem (M := M) f k).Retraction k where
  inv S := cechMap f (le_of_eq (Finset.insert_idem k S))
  inv_map S x := by
    have h := (cechCoeffSystem (M := M) f).map_map
      (Finset.insert_subset_insert k (Finset.subset_insert k S))
      (le_of_eq (Finset.insert_idem k S)) x
    rw [cechCoeffSystem_map, cechCoeffSystem_map, cechCoeffSystem_map] at h
    rw [cechShiftCoeffSystem_map, h]
    exact (cechCoeffSystem (M := M) f).map_self (le_refl (insert k S)) x
  map_inv S x := by
    have h := (cechCoeffSystem (M := M) f).map_map
      (le_of_eq (Finset.insert_idem k S))
      (Finset.insert_subset_insert k (Finset.subset_insert k S)) x
    rw [cechCoeffSystem_map, cechCoeffSystem_map, cechCoeffSystem_map] at h
    rw [cechShiftCoeffSystem_map, h]
    exact (cechCoeffSystem (M := M) f).map_self (le_refl (insert k (insert k S))) x
  inv_naturality {S T} h x := by
    have h₁ := (cechCoeffSystem (M := M) f).map_map
      (Finset.insert_subset_insert k (Finset.insert_subset_insert k h))
      (le_of_eq (Finset.insert_idem k T)) x
    have h₂ := (cechCoeffSystem (M := M) f).map_map
      (le_of_eq (Finset.insert_idem k S))
      (Finset.insert_subset_insert k h) x
    rw [cechCoeffSystem_map, cechCoeffSystem_map, cechCoeffSystem_map] at h₁ h₂
    rw [cechShiftCoeffSystem_map, cechShiftCoeffSystem_map, h₁, h₂]

/-- **The Čech complex with one index always inverted is exact.** Every cocycle is a
coboundary — this is the shape the Čech complex of a covering family takes after localizing at
one member of the family, and the reason the family's own Čech complex is exact. -/
theorem coeffD_shift_of_coeffD_eq_zero (k : ι)
    (g : ∀ S : Finset ι, cechObj f (M := M) (insert k S))
    (hg : ∀ S, (cechShiftCoeffSystem f k).coeffD g S = 0) (S : Finset ι) :
    (cechShiftCoeffSystem f k).coeffD ((cechShiftRetraction f k).coeffH g) S = g S :=
  (cechShiftRetraction f k).coeffD_coeffH_of_coeffD_eq_zero g hg S

variable {f}

/-! ## The shift map is a localization -/

variable (f)

/-- The comparison from the Čech complex to its shift at `k`, as a single linear map on the
product of all the Čech groups. -/
noncomputable def cechShiftₗ (k : ι) :
    (∀ S : Finset ι, cechObj f (M := M) S) →ₗ[R]
      (∀ S : Finset ι, cechObj f (M := M) (insert k S)) :=
  LinearMap.pi fun S => (cechMap f (Finset.subset_insert k S)).comp (LinearMap.proj S)

/-- **The shift map is localization at `f k`.** -/
instance isLocalizedModule_cechShiftₗ [Fintype ι] (k : ι) :
    IsLocalizedModule (Submonoid.powers (f k)) (cechShiftₗ f (M := M) k) :=
  IsLocalizedModule.pi _ _

/-- The shift map intertwines the two simplicial differentials. -/
lemma cechShiftₗ_coeffDₗ (k : ι) :
    (cechShiftₗ f (M := M) k).comp (cechCoeffSystem f).coeffDₗ
      = ((cechShiftCoeffSystem f k).coeffDₗ).comp (cechShiftₗ f k) := by
  refine LinearMap.ext fun g => funext fun S => ?_
  simp only [LinearMap.comp_apply, cechShiftₗ, LinearMap.pi_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.proj_apply, Finset.CoeffSystem.coeffDₗ_apply,
    Finset.CoeffSystem.coeffD, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  rw [cechCoeffSystem_map, cechShiftCoeffSystem_map, cechMap_cechMap, cechMap_cechMap]

variable {f}

/-! ## Exactness on a chart -/

/-- **The Čech complex of a family one of whose members is a unit is exact.** Every cocycle is
the coboundary of the cone off that member.

This is the computation on a single chart `D(f_v)` of an affine cover: there `f v` is
invertible, so the cover contains the whole space and the Čech complex contracts. Combined with
locality of exactness (`exact_of_localized_span`) over a spanning family, it gives the vanishing
of Čech cohomology of a quasi-coherent sheaf on an affine scheme. -/
theorem coeffD_cechH_of_isUnit (hv : IsUnit (f v))
    (g : ∀ S : Finset ι, cechObj f (M := M) S)
    (hg : ∀ S, (cechCoeffSystem f).coeffD g S = 0) (S : Finset ι) :
    (cechCoeffSystem f).coeffD ((cechRetraction hv).coeffH g) S = g S :=
  (cechRetraction hv).coeffD_coeffH_of_coeffD_eq_zero g hg S

/-! ## Exactness of the Čech complex of a covering family -/

variable (f)

/-- **The Čech complex of a covering family is exact.**

For `f : ι → R` a finite family generating the unit ideal — that is, the distinguished opens
`D(f i)` cover `Spec R` — and any `R`-module `M`, the complex

`⋯ → ⨁_{|S| = p} M[1/f_S] → ⨁_{|S| = p+1} M[1/f_S] → ⋯`

is exact. Localizing at `f k` turns it into the Čech complex of the shifted system, which is
contractible because `insert k` is idempotent; exactness then descends because the `f i`
generate the unit ideal (`exact_of_isLocalized_span`).

This is the vanishing of Čech cohomology of a quasi-coherent sheaf on an affine scheme with
respect to a cover by distinguished opens — the computation Cartan's criterion turns into the
vanishing of its derived cohomology. -/
theorem exact_coeffDₗ_cechCoeffSystem [Fintype ι]
    (hspan : Ideal.span (Set.range f) = ⊤) :
    Function.Exact (cechCoeffSystem (M := M) f).coeffDₗ
      (cechCoeffSystem (M := M) f).coeffDₗ := by
  classical
  have hk : ∀ r : (Set.range f : Set R), ∃ i : ι, f i = (r : R) := fun r => r.2
  choose kk hkk using hk
  haveI hloc : ∀ r : (Set.range f : Set R),
      IsLocalizedModule.Away (r : R) (cechShiftₗ f (M := M) (kk r)) := by
    intro r
    rw [← hkk r]
    infer_instance
  refine exact_of_isLocalized_span (Set.range f) hspan
    (fun r => ∀ S : Finset ι, cechObj f (M := M) (insert (kk r) S))
    (fun r => cechShiftₗ f (M := M) (kk r))
    (fun r => ∀ S : Finset ι, cechObj f (M := M) (insert (kk r) S))
    (fun r => cechShiftₗ f (M := M) (kk r))
    (fun r => ∀ S : Finset ι, cechObj f (M := M) (insert (kk r) S))
    (fun r => cechShiftₗ f (M := M) (kk r))
    _ _ fun r => ?_
  have hmap : IsLocalizedModule.map (Submonoid.powers (r : R))
      (cechShiftₗ f (M := M) (kk r)) (cechShiftₗ f (M := M) (kk r))
      (cechCoeffSystem (M := M) f).coeffDₗ
        = (cechShiftCoeffSystem f (kk r)).coeffDₗ := by
    refine IsLocalizedModule.ext (Submonoid.powers (r : R))
      (cechShiftₗ f (M := M) (kk r))
      (IsLocalizedModule.map_units (S := Submonoid.powers (r : R))
        (cechShiftₗ f (M := M) (kk r))) ?_
    exact (IsLocalizedModule.map_comp (S := Submonoid.powers (r : R))
      (f := cechShiftₗ f (M := M) (kk r)) (g := cechShiftₗ f (M := M) (kk r))
      (cechCoeffSystem (M := M) f).coeffDₗ).trans (cechShiftₗ_coeffDₗ f (kk r))
  rw [hmap]
  exact (cechShiftRetraction f (kk r)).exact_coeffDₗ

variable {f}

end LocalizedModule

end
