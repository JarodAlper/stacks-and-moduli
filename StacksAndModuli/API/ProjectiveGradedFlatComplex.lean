module

public import StacksAndModuli.API.ProjectiveGradedFlat

/-!
# Base change of a bounded exact complex of flat modules

Supporting API with no Stacks Project counterpart: the elementary core of **Cohomology and
Base Change** (§A.6, `thm:cbc`) in the graded Čech model.

Let `C⁰ → C¹ → ⋯` be a cochain complex of flat `R`-modules which vanishes above some degree
`N` and is exact everywhere except possibly at `C⁰`. Writing `Zⁱ = ker(dⁱ)`, the short exact
sequences

`0 → Zⁱ → Cⁱ → Zⁱ⁺¹ → 0`

let one descend from the top: `Z^{N+1} = 0` is flat, and if `Zⁱ⁺¹` is flat then so is `Zⁱ`
(`Module.Flat.of_shortExact`). Once every `Zⁱ` is flat, each of those sequences stays exact
after `A ⊗_R -` for **every** `R`-algebra `A` — no flatness of `A` is involved, only
`LinearMap.lTensor_injective_of_exact_of_flat` — and the conclusion is that `A ⊗_R C⁰⁻ᵗʰ`
still computes: the base-changed complex is exact in positive degrees, and its `H⁰` is
`A ⊗_R H⁰(C)`.

Applied to the Čech complex of a coherent flat family whose fibres have no higher cohomology,
this is exactly Cohomology and Base Change.

Main declarations:
- `CochainComplex.cocyclesSub`, `CochainComplex.dToCocycles`;
- `CochainComplex.flat_cocyclesSub`;
- `CochainComplex.range_baseChange_d_eq_ker`, `CochainComplex.ker_baseChange_d_zero`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace.CochainComplex

open CategoryTheory TensorProduct

variable {R : Type u} [CommRing R] (C : CochainComplex (ModuleCat.{u} R) ℕ)

/-- The `i`-th cocycles of a cochain complex, as a submodule. -/
def cocyclesSub (i : ℕ) : Submodule R (C.X i) := LinearMap.ker (C.d i (i + 1)).hom

lemma d_comp_d_apply (i : ℕ) (x : C.X i) :
    (C.d (i + 1) (i + 2)).hom ((C.d i (i + 1)).hom x) = 0 := by
  have h := congrArg ModuleCat.Hom.hom (C.d_comp_d i (i + 1) (i + 2))
  rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
  exact LinearMap.congr_fun h x

/-- The differential, corestricted to the cocycles of the next degree. -/
def dToCocycles (i : ℕ) : (C.X i : Type u) →ₗ[R] (cocyclesSub C (i + 1)) :=
  LinearMap.codRestrict _ (C.d i (i + 1)).hom (fun x => d_comp_d_apply C i x)

@[simp] lemma dToCocycles_val (i : ℕ) (x : C.X i) :
    ((dToCocycles C i x : cocyclesSub C (i + 1)) : C.X (i + 1)) = (C.d i (i + 1)).hom x := rfl

lemma ker_dToCocycles (i : ℕ) : LinearMap.ker (dToCocycles C i) = cocyclesSub C i := by
  ext x
  simp [dToCocycles, cocyclesSub, LinearMap.mem_ker, Subtype.ext_iff]

lemma exact_subtype_dToCocycles (i : ℕ) :
    Function.Exact (cocyclesSub C i).subtype (dToCocycles C i) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, (ker_dToCocycles C i) ▸ hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact Subtype.ext (LinearMap.mem_ker.mp y.2)

/-- Exactness of the complex at degree `i + 1`, in the form used here. -/
def ExactAtSucc (i : ℕ) : Prop :=
  LinearMap.range (C.d i (i + 1)).hom = cocyclesSub C (i + 1)

lemma surjective_dToCocycles {i : ℕ} (hex : ExactAtSucc C i) :
    Function.Surjective (dToCocycles C i) := by
  rintro ⟨z, hz⟩
  obtain ⟨x, hx⟩ : z ∈ LinearMap.range (C.d i (i + 1)).hom := hex ▸ hz
  exact ⟨x, Subtype.ext hx⟩


/-! ## Flatness of the cocycles, by descending induction

Everything below is stated relative to a threshold `t`: the complex is only assumed exact in
degrees `> t`, which is what the descending induction of the next section can offer at each
stage. -/

variable {C}

/-- **The cocycles of a bounded complex of flat modules, exact from `t` on, are flat from `t`
on.**

Descending induction from the vanishing range: `Zⁱ` for `i > N` is a submodule of the zero
module, and each `0 → Zⁱ → Cⁱ → Zⁱ⁺¹ → 0` exhibits `Zⁱ` as the kernel of a surjection between
flat modules with flat quotient. -/
lemma flat_cocyclesSub_aux (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) (N : ℕ)
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p)) {t : ℕ}
    (hex : ∀ i : ℕ, t ≤ i → ExactAtSucc C i) :
    ∀ (m i : ℕ), t ≤ i → N + 1 ≤ i + m → Module.Flat R (cocyclesSub C i) := by
  intro m
  induction m with
  | zero =>
      intro i _ hi
      haveI : Subsingleton (C.X i) := hvan i (by omega)
      haveI : Subsingleton (cocyclesSub C i) := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
      exact Module.Flat.of_shrink.{u, u, u}
  | succ m ih =>
      intro i hti hi
      rcases lt_or_ge N i with hNi | hNi
      · haveI : Subsingleton (C.X i) := hvan i hNi
        haveI : Subsingleton (cocyclesSub C i) :=
          ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
        exact Module.Flat.of_shrink.{u, u, u}
      · haveI := hflat i
        haveI := ih (i + 1) (by omega) (by omega)
        exact Module.Flat.of_shortExact (cocyclesSub C i).subtype (dToCocycles C i)
          Subtype.val_injective (exact_subtype_dToCocycles C i)
          (surjective_dToCocycles C (hex i hti))

/-- **The cocycles of a bounded complex of flat modules, exact from `t` on, are flat from `t`
on.** -/
lemma flat_cocyclesSub (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p)) {t : ℕ}
    (hex : ∀ i : ℕ, t ≤ i → ExactAtSucc C i) {i : ℕ} (hi : t ≤ i) :
    Module.Flat R (cocyclesSub C i) :=
  flat_cocyclesSub_aux hflat N hvan hex (N + 1) i hi (by omega)

/-! ## What survives an arbitrary base change -/

variable (A : Type u) [CommRing A] [Algebra R A]

/-- After base change the cocycle inclusion is still injective: the quotient `Zⁱ⁺¹` is flat, so
the sequence `0 → Zⁱ → Cⁱ → Zⁱ⁺¹ → 0` is pure. -/
lemma injective_baseChange_cocyclesSub_subtype
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p)) {t : ℕ}
    (hex : ∀ i : ℕ, t ≤ i → ExactAtSucc C i) {i : ℕ} (hi : t ≤ i) :
    Function.Injective (LinearMap.baseChange A (cocyclesSub C i).subtype) := by
  haveI := flat_cocyclesSub hflat hvan hex (i := i + 1) (by omega)
  have h := LinearMap.lTensor_injective_of_exact_of_flat (dToCocycles C i)
    (surjective_dToCocycles C (hex i hi)) (cocyclesSub C i).subtype Subtype.val_injective
    (exact_subtype_dToCocycles C i) A
  intro x y hxy
  refine h ?_
  simpa only [LinearMap.baseChange_eq_ltensor] using hxy

/-- The image of the base-changed differential is the base change of the cocycles. -/
lemma range_baseChange_d {t : ℕ} (hex : ∀ i : ℕ, t ≤ i → ExactAtSucc C i) {i : ℕ} (hi : t ≤ i) :
    LinearMap.range (LinearMap.baseChange A (C.d i (i + 1)).hom)
      = LinearMap.range (LinearMap.baseChange A (cocyclesSub C (i + 1)).subtype) := by
  have hfac : (C.d i (i + 1)).hom
      = (cocyclesSub C (i + 1)).subtype ∘ₗ dToCocycles C i := rfl
  rw [hfac, LinearMap.baseChange_comp, LinearMap.range_comp,
    LinearMap.range_eq_top.mpr
      (LinearMap.baseChange_surjective A (surjective_dToCocycles C (hex i hi))),
    Submodule.map_top]

/-- The kernel of the base-changed differential is the base change of the cocycles. -/
lemma ker_baseChange_d (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p)) {t : ℕ}
    (hex : ∀ i : ℕ, t ≤ i → ExactAtSucc C i) {i : ℕ} (hi : t ≤ i) :
    LinearMap.ker (LinearMap.baseChange A (C.d i (i + 1)).hom)
      = LinearMap.range (LinearMap.baseChange A (cocyclesSub C i).subtype) := by
  have hfac : (C.d i (i + 1)).hom
      = (cocyclesSub C (i + 1)).subtype ∘ₗ dToCocycles C i := rfl
  have hexA : Function.Exact (LinearMap.baseChange A (cocyclesSub C i).subtype)
      (LinearMap.baseChange A (dToCocycles C i)) := by
    have h := lTensor_exact A (exact_subtype_dToCocycles C i)
      (surjective_dToCocycles C (hex i hi))
    intro x
    simpa only [LinearMap.baseChange_eq_ltensor] using h x
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · refine (hexA x).mp ?_
    have hinj := injective_baseChange_cocyclesSub_subtype A hflat hvan hex (i := i + 1)
      (by omega)
    refine hinj ?_
    rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← hfac]
    exact hx
  · have h0 : (LinearMap.baseChange A (dToCocycles C i)) x = 0 := (hexA x).mpr hx
    rw [LinearMap.mem_ker, hfac, LinearMap.baseChange_comp, LinearMap.comp_apply, h0,
      map_zero]

/-- **The base change of a bounded exact complex of flat modules is exact in every positive
degree.** -/
theorem range_baseChange_d_eq_ker (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p)) {t : ℕ}
    (hex : ∀ i : ℕ, t ≤ i → ExactAtSucc C i) {i : ℕ} (hi : t ≤ i) :
    LinearMap.range (LinearMap.baseChange A (C.d i (i + 1)).hom)
      = LinearMap.ker (LinearMap.baseChange A (C.d (i + 1) (i + 2)).hom) := by
  rw [range_baseChange_d A hex hi, ker_baseChange_d A hflat hvan hex (i := i + 1) (by omega)]

/-! ## From fibrewise exactness to exactness over the base -/

variable (C)

/-- `H^{j+1}(C)` as a concrete quotient module: the cocycles in degree `j + 1` modulo the
image of the differential out of degree `j`. -/
abbrev cohomologySucc (j : ℕ) : Type u :=
  (cocyclesSub C (j + 1)) ⧸ (LinearMap.range (dToCocycles C j))

lemma subsingleton_cohomologySucc_iff (j : ℕ) :
    Subsingleton (cohomologySucc C j) ↔ ExactAtSucc C j := by
  rw [Submodule.Quotient.subsingleton_iff, ExactAtSucc]
  constructor
  · intro h
    refine le_antisymm (fun x hx => ?_) (fun z hz => ?_)
    · obtain ⟨y, hy⟩ := hx
      rw [← hy]
      exact (dToCocycles C j y).2
    · obtain ⟨y, hy⟩ : (⟨z, hz⟩ : cocyclesSub C (j + 1)) ∈
          LinearMap.range (dToCocycles C j) := h ▸ Submodule.mem_top
      exact ⟨y, congrArg Subtype.val hy⟩
  · intro h
    exact LinearMap.range_eq_top.mpr (surjective_dToCocycles C h)

/-- The base-changed complex has the same differentials, up to `ModuleCat.ofHom`. -/
lemma cochainBaseChange_d_hom (A : Type u) [CommRing A] [Algebra R A] (j : ℕ) :
    ((GradedModule.cochainBaseChange A C).d j (j + 1)).hom
      = LinearMap.baseChange A (C.d j (j + 1)).hom := by
  rw [GradedModule.cochainBaseChange_d]
  rfl

/-- **The descending step.** If the complex is already exact above degree `j + 1`, then
exactness of the base-changed complex at `j + 1` forces `A ⊗ H^{j+1}(C)` to vanish.

Only right exactness of `A ⊗ -` is used: exactness of `C ⊗ A` at `j + 1` says that
`A ⊗ Cʲ → A ⊗ Z^{j+1}` is onto (the cocycle inclusion stays injective because `Z^{j+2}` is
flat), and `A ⊗ H^{j+1}(C)` is a quotient of `A ⊗ Z^{j+1}` killed by that image. -/
theorem subsingleton_baseChange_cohomologySucc
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (j : ℕ) (habove : ∀ i : ℕ, j + 1 ≤ i → ExactAtSucc C i)
    (A : Type u) [CommRing A] [Algebra R A]
    (hA : ExactAtSucc (GradedModule.cochainBaseChange A C) j) :
    Subsingleton (A ⊗[R] (cohomologySucc C j)) := by
  haveI hZ2 : Module.Flat R (cocyclesSub C (j + 2)) :=
    flat_cocyclesSub (C := C) hflat hvan habove (i := j + 2) (by omega)
  -- exactness of the base change at `j + 1`, spelled out
  have hAe : LinearMap.range (LinearMap.baseChange A (C.d j (j + 1)).hom)
      = LinearMap.ker (LinearMap.baseChange A (C.d (j + 1) (j + 2)).hom) := by
    have h := hA
    rw [ExactAtSucc, cocyclesSub, cochainBaseChange_d_hom, cochainBaseChange_d_hom] at h
    exact h
  -- both sides are images of the cocycle inclusion
  have hker : LinearMap.ker (LinearMap.baseChange A (C.d (j + 1) (j + 2)).hom)
      = Submodule.map (LinearMap.baseChange A (cocyclesSub C (j + 1)).subtype) ⊤ := by
    rw [Submodule.map_top]
    exact ker_baseChange_d A hflat hvan habove (i := j + 1) le_rfl
  have hrange : LinearMap.range (LinearMap.baseChange A (C.d j (j + 1)).hom)
      = Submodule.map (LinearMap.baseChange A (cocyclesSub C (j + 1)).subtype)
          (LinearMap.range (LinearMap.baseChange A (dToCocycles C j))) := by
    have hfac : (C.d j (j + 1)).hom
        = (cocyclesSub C (j + 1)).subtype ∘ₗ dToCocycles C j := rfl
    rw [hfac, LinearMap.baseChange_comp, LinearMap.range_comp]
  -- the cocycle inclusion is injective after base change, so the differential is onto
  have hinj := injective_baseChange_cocyclesSub_subtype A hflat hvan habove
    (i := j + 1) le_rfl
  have hsurj : Function.Surjective (LinearMap.baseChange A (dToCocycles C j)) := by
    rw [← LinearMap.range_eq_top]
    refine Submodule.map_injective_of_injective hinj ?_
    rw [← hrange, hAe, hker]
  -- `A ⊗ H^{j+1}` is a quotient of `A ⊗ Z^{j+1}` killed by that image
  refine ⟨fun a b => ?_⟩
  have hq : Function.Surjective
      (LinearMap.baseChange A (LinearMap.range (dToCocycles C j)).mkQ) :=
    LinearMap.baseChange_surjective A (Submodule.mkQ_surjective _)
  have hzero : ∀ z, (LinearMap.baseChange A
      (LinearMap.range (dToCocycles C j)).mkQ) z = 0 := by
    intro z
    obtain ⟨w, rfl⟩ := hsurj z
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    have : (LinearMap.range (dToCocycles C j)).mkQ ∘ₗ dToCocycles C j = 0 := by
      refine LinearMap.ext fun x => ?_
      exact (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self _ _)
    rw [this]
    simp
  obtain ⟨a', rfl⟩ := hq a
  obtain ⟨b', rfl⟩ := hq b
  rw [hzero, hzero]

lemma exactAtSucc_of_subsingleton_X {C : CochainComplex (ModuleCat.{u} R) ℕ} {j : ℕ}
    (h : Subsingleton (C.X (j + 1))) : ExactAtSucc C j := by
  haveI := h
  refine le_antisymm (fun x _ => ?_) (fun x _ => ?_) <;>
    · rw [Subsingleton.elim x 0]
      exact Submodule.zero_mem _

/-- **Fibrewise exactness implies exactness over the base**, for a bounded complex of flat
modules with finite cohomology.

This is the direction Cohomology and Base Change needs, and the reason it is available without
constructing a finite free "Grothendieck complex": the comparison
`Hⁱ(C ⊗ A) ≅ Hⁱ(C) ⊗ A` is *right exact* at the top of the complex, so a descending induction
gets it at every stage, and Nakayama over all residue fields
(`Module.subsingleton_of_forall_quotient_maximal`) converts fibrewise vanishing into
vanishing over `R`. -/
theorem exactAtSucc_of_fibrewise
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hfin : ∀ j : ℕ, Module.Finite R (cohomologySucc C j))
    (hfib : ∀ (κ : Type u) [Field κ] [Algebra R κ] (j : ℕ),
      ExactAtSucc (GradedModule.cochainBaseChange κ C) j) :
    ∀ j : ℕ, ExactAtSucc C j := by
  have key : ∀ (m j : ℕ), N ≤ j + m → ExactAtSucc C j := by
    intro m
    induction m with
    | zero =>
        intro j hj
        exact exactAtSucc_of_subsingleton_X (hvan (j + 1) (by omega))
    | succ m ih =>
        intro j hj
        rcases le_or_gt N j with hNj | hNj
        · exact exactAtSucc_of_subsingleton_X (hvan (j + 1) (by omega))
        · have habove : ∀ i : ℕ, j + 1 ≤ i → ExactAtSucc C i :=
            fun i hi => ih i (by omega)
          rw [← subsingleton_cohomologySucc_iff]
          haveI : Module.Finite R (cohomologySucc C j) := hfin j
          refine Module.subsingleton_of_forall_quotient_maximal (R := R) (fun m' hm' => ?_)
          letI : Field (R ⧸ m') := @Ideal.Quotient.field _ _ m' hm'
          have hA : ExactAtSucc (GradedModule.cochainBaseChange (R ⧸ m') C) j :=
            hfib (R ⧸ m') j
          exact subsingleton_baseChange_cohomologySucc C hflat hvan j habove (R ⧸ m') hA
  exact fun j => key N j (by omega)

/-! ## `H⁰` and base change -/

/-- The cocycles of the base-changed complex, spelled with `LinearMap.baseChange`. -/
lemma cocyclesSub_cochainBaseChange (A : Type u) [CommRing A] [Algebra R A] (i : ℕ) :
    cocyclesSub (GradedModule.cochainBaseChange A C) i
      = LinearMap.ker (LinearMap.baseChange A (C.d i (i + 1)).hom) :=
  congrArg LinearMap.ker (cochainBaseChange_d_hom C A i)

/-- The cocycles of the base-changed complex are the base change of the cocycles. -/
lemma range_baseChange_cocyclesSub_subtype_eq
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hex : ∀ i : ℕ, ExactAtSucc C i) (A : Type u) [CommRing A] [Algebra R A] (i : ℕ) :
    LinearMap.range (LinearMap.baseChange A (cocyclesSub C i).subtype)
      = cocyclesSub (GradedModule.cochainBaseChange A C) i := by
  rw [cocyclesSub_cochainBaseChange]
  exact (ker_baseChange_d A hflat hvan (t := 0) (fun i' _ => hex i') (Nat.zero_le i)).symm

/-- **`H⁰` commutes with base change**, along an arbitrary ring map: for a bounded complex of
flat modules that is exact in positive degrees, `A ⊗_R H⁰(C) ≅ H⁰(C ⊗_R A)`.

This is the isomorphism behind `RelativeCohomology.CommutesWithBaseChange`. -/
noncomputable def cocyclesBaseChangeEquiv
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hex : ∀ i : ℕ, ExactAtSucc C i) (A : Type u) [CommRing A] [Algebra R A] (i : ℕ) :
    (A ⊗[R] (cocyclesSub C i)) ≃ₗ[A] (cocyclesSub (GradedModule.cochainBaseChange A C) i) :=
  (LinearEquiv.ofInjective (LinearMap.baseChange A (cocyclesSub C i).subtype)
      (injective_baseChange_cocyclesSub_subtype A hflat hvan (t := 0)
        (fun i' _ => hex i') (Nat.zero_le i))).trans
    (LinearEquiv.ofEq _ _ (range_baseChange_cocyclesSub_subtype_eq C hflat hvan hex A i))

/-- `H⁰` of a bounded exact-in-positive-degrees complex of flat modules is flat. -/
lemma flat_cocyclesSub_zero (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hex : ∀ i : ℕ, ExactAtSucc C i) (i : ℕ) : Module.Flat R (cocyclesSub C i) :=
  flat_cocyclesSub hflat hvan (t := 0) (fun i' _ => hex i') (Nat.zero_le i)

/-- `H⁰` of a bounded exact-in-positive-degrees complex of flat modules with finite `H⁰` is
finite **projective** over the base. -/
lemma projective_cocyclesSub (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hex : ∀ i : ℕ, ExactAtSucc C i) [IsNoetherianRing R] (i : ℕ)
    [Module.Finite R (cocyclesSub C i)] : Module.Projective R (cocyclesSub C i) := by
  haveI := flat_cocyclesSub_zero C hflat hvan hex i
  haveI : Module.FinitePresentation R (cocyclesSub C i) :=
    Module.finitePresentation_of_finite R _
  exact Module.Flat.projective_of_finitePresentation

/-! ## Comparison with the abstract `homology` -/

/-- The abstract homology in degree `j + 1` agrees with the concrete quotient
`Z^{j+1} ⧸ im dʲ`. -/
noncomputable def homologySuccEquiv (j : ℕ) :
    ((C.homology (j + 1) : ModuleCat.{u} R) : Type u) ≃ₗ[R] cohomologySucc C j :=
  ((C.homologyIsoSc' j (j + 1) (j + 2) (by simp) (by simp)).trans
    (C.sc' j (j + 1) (j + 2)).moduleCatHomologyIso).toLinearEquiv

/-- The abstract homology in degree `0` is the cocycles: nothing maps into degree `0`. -/
noncomputable def homologyZeroEquiv :
    ((C.homology 0 : ModuleCat.{u} R) : Type u) ≃ₗ[R] cocyclesSub C 0 := by
  refine (((C.homologyIsoSc' 0 0 1 (by simp) (by simp)).trans
    (C.sc' 0 0 1).moduleCatHomologyIso).toLinearEquiv).trans (Submodule.quotEquivOfEqBot _ ?_)
  rw [LinearMap.range_eq_bot]
  refine LinearMap.ext fun x => Subtype.ext ?_
  have h0 : C.d 0 0 = 0 := C.shape 0 0 (by simp)
  change ((C.d 0 0).hom) x = 0
  rw [h0]
  rfl

lemma subsingleton_homology_succ_iff (j : ℕ) :
    Subsingleton (C.homology (j + 1)) ↔ ExactAtSucc C j := by
  rw [← subsingleton_cohomologySucc_iff]
  exact (homologySuccEquiv C j).toEquiv.subsingleton_congr

lemma finite_cohomologySucc (j : ℕ) [Module.Finite R (C.homology (j + 1))] :
    Module.Finite R (cohomologySucc C j) :=
  Module.Finite.equiv (homologySuccEquiv C j)

lemma finite_cocyclesSub_zero [Module.Finite R (C.homology 0)] :
    Module.Finite R (cocyclesSub C 0) :=
  Module.Finite.equiv (homologyZeroEquiv C)

/-! ## Naturality of the comparison with `homology` -/

/-- Naturality of `HomologicalComplex.homologyIsoSc'` in the complex. -/
lemma homologyIsoSc'_naturality {K L : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L)
    (i j k : ℕ) (hi : (ComplexShape.up ℕ).prev j = i)
    (hk : (ComplexShape.up ℕ).next j = k) :
    HomologicalComplex.homologyMap φ j ≫ (L.homologyIsoSc' i j k hi hk).hom
      = (K.homologyIsoSc' i j k hi hk).hom
        ≫ ShortComplex.homologyMap
            ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R)
              (ComplexShape.up ℕ) i j k).map φ) := by
  subst hi
  subst hk
  have hnat := (HomologicalComplex.natIsoSc' (ModuleCat.{u} R) (ComplexShape.up ℕ)
    ((ComplexShape.up ℕ).prev j) j ((ComplexShape.up ℕ).next j) rfl rfl).hom.naturality φ
  have h1 : ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) j).map φ ≫
        (HomologicalComplex.natIsoSc' (ModuleCat.{u} R) (ComplexShape.up ℕ)
          ((ComplexShape.up ℕ).prev j) j ((ComplexShape.up ℕ).next j) rfl rfl).hom.app L)
      = ShortComplex.homologyMap
        ((HomologicalComplex.natIsoSc' (ModuleCat.{u} R) (ComplexShape.up ℕ)
            ((ComplexShape.up ℕ).prev j) j ((ComplexShape.up ℕ).next j) rfl rfl).hom.app K ≫
          (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (ComplexShape.up ℕ)
            ((ComplexShape.up ℕ).prev j) j ((ComplexShape.up ℕ).next j)).map φ) := by rw [hnat]
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at h1
  exact h1

/-- The inverse of `homologyZeroEquiv`, spelled out. -/
lemma homologyZeroEquiv_symm_eq (K : CochainComplex (ModuleCat.{u} R) ℕ)
    (z : cocyclesSub K 0) :
    (homologyZeroEquiv K).symm z
      = (K.homologyIsoSc' 0 0 1 (by simp) (by simp)).inv.hom
          ((ShortComplex.moduleCatHomologyIso (K.sc' 0 0 1)).toLinearEquiv.symm
            (Submodule.Quotient.mk z)) := rfl

lemma homologyIsoSc'_inv_hom (K : CochainComplex (ModuleCat.{u} R) ℕ)
    (x : (K.sc' 0 0 1).homology) :
    (K.homologyIsoSc' 0 0 1 (by simp) (by simp)).hom.hom
      ((K.homologyIsoSc' 0 0 1 (by simp) (by simp)).inv.hom x) = x := by
  have h := congrArg ModuleCat.Hom.hom
    (K.homologyIsoSc' 0 0 1 (by simp) (by simp)).inv_hom_id
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id] at h
  exact LinearMap.congr_fun h x

/-- **The comparison of `homology 0` with the cocycles is natural in the complex.** -/
lemma homologyZeroEquiv_symm_naturality {K L : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L)
    (z : cocyclesSub K 0) (hz : (φ.f 0).hom (z : K.X 0) ∈ cocyclesSub L 0) :
    (HomologicalComplex.homologyMap φ 0).hom ((homologyZeroEquiv K).symm z)
      = (homologyZeroEquiv L).symm ⟨(φ.f 0).hom (z : K.X 0), hz⟩ := by
  have hnat := congrArg ModuleCat.Hom.hom (homologyIsoSc'_naturality φ 0 0 1 (by simp) (by simp))
  simp only [ModuleCat.hom_comp] at hnat
  set w := (ShortComplex.moduleCatHomologyIso (K.sc' 0 0 1)).toLinearEquiv.symm
    (Submodule.Quotient.mk z) with hw
  refine (L.homologyIsoSc' 0 0 1 (by simp) (by simp)).toLinearEquiv.injective ?_
  rw [homologyZeroEquiv_symm_eq K z, homologyZeroEquiv_symm_eq L _]
  change (L.homologyIsoSc' 0 0 1 (by simp) (by simp)).hom.hom
      ((HomologicalComplex.homologyMap φ 0).hom
        ((K.homologyIsoSc' 0 0 1 (by simp) (by simp)).inv.hom w))
    = (L.homologyIsoSc' 0 0 1 (by simp) (by simp)).hom.hom
      ((L.homologyIsoSc' 0 0 1 (by simp) (by simp)).inv.hom
        ((ShortComplex.moduleCatHomologyIso (L.sc' 0 0 1)).toLinearEquiv.symm
          (Submodule.Quotient.mk ⟨(φ.f 0).hom (z : K.X 0), hz⟩)))
  rw [homologyIsoSc'_inv_hom L]
  have h1 := LinearMap.congr_fun hnat
    ((K.homologyIsoSc' 0 0 1 (by simp) (by simp)).inv.hom w)
  simp only [LinearMap.comp_apply] at h1
  rw [h1, homologyIsoSc'_inv_hom K, hw]
  exact GradedModule.moduleCatHomologyIso_symm_mk_naturality
    ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R)
      (ComplexShape.up ℕ) 0 0 1).map φ) z hz

/-! ## Naturality of the cocycle base-change comparison -/

/-- A chain map restricts to the cocycles. -/
def cocyclesMap {K L : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L) (i : ℕ) :
    (cocyclesSub K i) →ₗ[R] (cocyclesSub L i) :=
  LinearMap.restrict (φ.f i).hom (fun x hx => by
    have h := congrArg ModuleCat.Hom.hom (φ.comm i (i + 1))
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at h
    have := LinearMap.congr_fun h x
    simp only [LinearMap.comp_apply] at this
    simp only [cocyclesSub, LinearMap.mem_ker] at hx ⊢
    rw [this, hx, map_zero])

@[simp] lemma cocyclesMap_val {K L : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L) (i : ℕ)
    (x : cocyclesSub K i) : ((cocyclesMap φ i x : cocyclesSub L i) : L.X i)
      = (φ.f i).hom (x : K.X i) := rfl

/-- **The comparison of `homology 0` with the cocycles is natural**, forward direction. -/
lemma homologyZeroEquiv_naturality {K L : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L)
    (y : K.homology 0) :
    (homologyZeroEquiv L) ((HomologicalComplex.homologyMap φ 0).hom y)
      = cocyclesMap φ 0 (homologyZeroEquiv K y) := by
  obtain ⟨z, rfl⟩ := (homologyZeroEquiv K).symm.surjective y
  rw [homologyZeroEquiv_symm_naturality φ z (cocyclesMap φ 0 z).2,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  rfl

lemma cocyclesBaseChangeEquiv_val
    (hflat : ∀ p : ℕ, Module.Flat R (C.X p)) {N : ℕ}
    (hvan : ∀ p : ℕ, N < p → Subsingleton (C.X p))
    (hex : ∀ i : ℕ, ExactAtSucc C i) (A : Type u) [CommRing A] [Algebra R A] (i : ℕ)
    (x : A ⊗[R] (cocyclesSub C i)) :
    ((cocyclesBaseChangeEquiv C hflat hvan hex A i x :
        cocyclesSub (GradedModule.cochainBaseChange A C) i)
      : (GradedModule.cochainBaseChange A C).X i)
      = LinearMap.baseChange A (cocyclesSub C i).subtype x := rfl

/-- **The cocycle base-change comparison is natural in the complex.** -/
lemma cocyclesBaseChangeEquiv_naturality
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L)
    (hKflat : ∀ p : ℕ, Module.Flat R (K.X p)) {NK : ℕ}
    (hKvan : ∀ p : ℕ, NK < p → Subsingleton (K.X p))
    (hKex : ∀ i : ℕ, ExactAtSucc K i)
    (hLflat : ∀ p : ℕ, Module.Flat R (L.X p)) {NL : ℕ}
    (hLvan : ∀ p : ℕ, NL < p → Subsingleton (L.X p))
    (hLex : ∀ i : ℕ, ExactAtSucc L i)
    (A : Type u) [CommRing A] [Algebra R A] (i : ℕ) (x : A ⊗[R] (cocyclesSub K i)) :
    ((cocyclesBaseChangeEquiv L hLflat hLvan hLex A i
          (LinearMap.baseChange A (cocyclesMap φ i) x) :
        cocyclesSub (GradedModule.cochainBaseChange A L) i)
      : (GradedModule.cochainBaseChange A L).X i)
      = ((GradedModule.cochainBaseChangeMap A φ).f i).hom
          ((cocyclesBaseChangeEquiv K hKflat hKvan hKex A i x :
            cocyclesSub (GradedModule.cochainBaseChange A K) i) : _) := by
  have key : (LinearMap.baseChange A (cocyclesSub L i).subtype) ∘ₗ
        (LinearMap.baseChange A (cocyclesMap φ i))
      = (LinearMap.baseChange A ((φ.f i).hom)) ∘ₗ
        (LinearMap.baseChange A (cocyclesSub K i).subtype) := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp]
    rfl
  exact LinearMap.congr_fun key x

end AlgebraicGeometry.ProjectiveSpace.CochainComplex

end
