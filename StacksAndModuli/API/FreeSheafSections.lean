module

public import StacksAndModuli.API.TwistMonomialSections
public import StacksAndModuli.API.ProjectiveTwistedFreeGlobalSectionsFinite
public import StacksAndModuli.«Section2.1-Intro».«part2.1.1-quasi-coherent-subsheaves»
public import StacksAndModuli.API.QuasicoherentSectionsQcqs

/-!
# Sections of a finite free sheaf over an open

`AlgebraicGeometry.Scheme.SubmoduleSheafData` — the kernel encoding used by
`grassmannianFunctor` — asks for a submodule of `Fin n → Γ(X, U)` for each affine open `U`.
A morphism out of a finite free sheaf gives one, its kernel, but only after `Γ(𝒪^I, U)` has
been identified with `I → Γ(X, U)`.

That identification is cheap once one notices two things: sections over a *fixed* open form an
additive functor `X.Modules ⥤ ModuleCat Γ(X, U)` (nothing about a base ring is needed — the
`Γ(X,U)`-module structure is the one the presheaf of modules already carries), and
`Γ(unit, U)` is *definitionally* `Γ(X, U)`.  A finite coproduct is a biproduct, an additive
functor preserves it, and the identification follows.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.openSectionsFunctor` and its `Additive` instance;
* `AlgebraicGeometry.Scheme.Modules.openSectionsFiniteCoproductLinearEquiv`;
* `AlgebraicGeometry.Scheme.Modules.freeSectionsEquiv` and
  `AlgebraicGeometry.Scheme.Modules.freeSectionsMap`;
* `AlgebraicGeometry.Scheme.Modules.finFreeSectionsMap` — the module map in the
  `freeSectionsEquiv` form, which is the one that identifies it with the sections of the free
  sheaf;
* `AlgebraicGeometry.Scheme.Modules.freeGen`, `…finFreeSectionsMap'` and
  `…freeGen_restrict` — the same module map written as `x ↦ ∑ i, x i • (generator i)`.  In
  this form linearity and **naturality in the open** are immediate, which is what the
  compatibility needs, so `kernelSubmodule` is defined from this version;
* `AlgebraicGeometry.Scheme.Modules.finFreeSectionsMap'_resPi`, `…resPi_mem_kernel` and
  `…span_resPi_kernel_le` — the `≤` half of `span_resPi_basicOpen`, pure naturality;
* `AlgebraicGeometry.Scheme.Modules.span_resPi_kernel_ge` — the `≥` half.  Clearing
  denominators against `IsAffineOpen.isLocalization_basicOpen` reduces it to: a section of
  `M` over `U` vanishing on `D(f)` is annihilated by a power of `f`.  **That is exactly
  quasicoherence of `M`**, and it is the only place the hypothesis is used;
* `AlgebraicGeometry.Scheme.Modules.span_resPi_kernel` and `…kernelSubmoduleSheafData` — the
  compatibility in full, and hence the kernel of `φ : 𝒪^m ⟶ M` as an unconditional
  `SubmoduleSheafData` for `M` quasicoherent.  For `M = π_*(F(d))` the quasicoherence
  hypothesis is discharged by `Modules.isQuasicoherent_pushforward_of_qcqs`
  (`API/QcqsPushforwardQuasicoherent.lean`), which applies because `π` is proper.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- Sections over a fixed open, as a functor to modules over the sections of the structure
sheaf there. -/
def openSectionsFunctor {X : Scheme.{u}} (U : X.Opens) :
    X.Modules ⥤ ModuleCat ↥Γ(X, U) where
  obj M := M.val.obj (op U)
  map φ := φ.val.app (op U)
  map_id _ := rfl
  map_comp _ _ := rfl

instance openSectionsFunctor_additive {X : Scheme.{u}} (U : X.Opens) :
    (openSectionsFunctor U).Additive where
  map_add := rfl

/-- Sections over an open identify a finite coproduct with the product of the components. -/
def openSectionsFiniteCoproductLinearEquiv {X : Scheme.{u}} {J : Type u} [Finite J]
    (U : X.Opens) (F : J → X.Modules) :
    Γ(∐ F, U) ≃ₗ[↥Γ(X, U)] (∀ j, ↥Γ(F j, U)) := by
  letI : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteCoproducts
  let G := openSectionsFunctor U
  letI : PreservesBiproduct F G :=
    let ⟨_⟩ := nonempty_fintype J
    { preserves := fun hb ↦
        ⟨isBilimitOfTotal _ (by
          simp_rw [G.mapBicone_π, G.mapBicone_ι, ← G.map_comp]
          erw [← G.map_sum, ← G.map_id, IsBilimit.total hb])⟩ }
  exact (G.mapIso (biproduct.isoCoproduct F).symm ≪≫
    G.mapBiproduct F ≪≫
    moduleCatBiproductIsoPi (G.obj ∘ F)).toLinearEquiv

/-- Sections of the unit sheaf over an open are the sections of the structure sheaf. -/
example {X : Scheme.{u}} (U : X.Opens) :
    Γ(SheafOfModules.unit X.ringCatSheaf, U) = ↥Γ(X, U) := rfl

/-- **Sections of a finite free sheaf over an open are tuples of sections of the structure
sheaf.**  This is the identification `SubmoduleSheafData` needs. -/
def freeSectionsEquiv {X : Scheme.{u}} {I : Type u} [Finite I] (U : X.Opens) :
    Γ(SheafOfModules.free (R := X.ringCatSheaf) I, U) ≃ₗ[↥Γ(X, U)] (I → ↥Γ(X, U)) :=
  openSectionsFiniteCoproductLinearEquiv U (fun _ : I => SheafOfModules.unit X.ringCatSheaf)

/-- **The module map on an open cut out by a morphism from a finite free sheaf.** -/
def freeSectionsMap {X : Scheme.{u}} {I : Type u} [Finite I] {M : X.Modules}
    (φ : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ M) (U : X.Opens) :
    (I → ↥Γ(X, U)) →ₗ[↥Γ(X, U)] ↥Γ(M, U) :=
  (PresheafOfModules.Hom.app φ.val (op U)).hom.comp (freeSectionsEquiv U).symm.toLinearMap

/-- The module map on an open cut out by a morphism from `𝒪^{Fin m}`, reindexed so that the
source is `Fin m → Γ(X, U)` as `SubmoduleSheafData` expects. -/
def finFreeSectionsMap {X : Scheme.{u}} {m : ℕ} {M : X.Modules}
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M) (U : X.Opens) :
    (Fin m → ↥Γ(X, U)) →ₗ[↥Γ(X, U)] ↥Γ(M, U) :=
  (freeSectionsMap φ U).comp
    (LinearEquiv.funCongrLeft ↥Γ(X, U) ↥Γ(X, U)
      (Equiv.ulift.{u, 0} (α := Fin m))).toLinearMap

/-- The `i`-th generating section cut out on an open by a morphism from `𝒪^{Fin m}`. -/
def freeGen {X : Scheme.{u}} {m : ℕ} {M : X.Modules}
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    (U : X.Opens) (i : Fin m) : ↥Γ(M, U) :=
  letI ψ : SheafOfModules.unit X.ringCatSheaf ⟶ M :=
    SheafOfModules.ιFree (ULift.up i) ≫ φ
  (PresheafOfModules.Hom.app ψ.val (op U)).hom (1 : ↥Γ(X, U))

/-- **The module map on an open**, written as a sum over the free generators.  In this form
it is manifestly linear and manifestly natural in the open. -/
def finFreeSectionsMap' {X : Scheme.{u}} {m : ℕ} {M : X.Modules}
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M) (U : X.Opens) :
    (Fin m → ↥Γ(X, U)) →ₗ[↥Γ(X, U)] ↥Γ(M, U) where
  toFun x := ∑ i : Fin m, x i • freeGen φ U i
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
    exact (Finset.smul_sum).symm

/-- The generating sections restrict to the generating sections. -/
lemma freeGen_restrict {X : Scheme.{u}} {m : ℕ} {M : X.Modules}
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    {U V : X.Opens} (h : V ≤ U) (i : Fin m) :
    M.val.map ((homOfLE h).op : op U ⟶ op V) (freeGen φ U i) = freeGen φ V i := by
  letI ψ : SheafOfModules.unit X.ringCatSheaf ⟶ M :=
    SheafOfModules.ιFree (ULift.up i) ≫ φ
  have hnat := ConcreteCategory.congr_hom
    (ψ.val.naturality ((homOfLE h).op : op U ⟶ op V)) (1 : ↥Γ(X, U))
  have hnat' : (PresheafOfModules.Hom.app ψ.val (op V)).hom
      ((SheafOfModules.unit X.ringCatSheaf).val.map ((homOfLE h).op : op U ⟶ op V)
        (1 : ↥Γ(X, U))) =
      M.val.map ((homOfLE h).op : op U ⟶ op V)
        ((PresheafOfModules.Hom.app ψ.val (op U)).hom (1 : ↥Γ(X, U))) := hnat
  have h1 : (SheafOfModules.unit X.ringCatSheaf).val.map ((homOfLE h).op : op U ⟶ op V)
      (1 : ↥Γ(X, U)) = (1 : ↥Γ(X, V)) := by
    change (X.presheaf.map ((homOfLE h).op : op U ⟶ op V)).hom (1 : ↥Γ(X, U)) = 1
    exact map_one _
  rw [h1] at hnat'
  exact hnat'.symm

/-- **The module map is natural in the open.** -/
lemma finFreeSectionsMap'_resPi {X : Scheme.{u}} {m : ℕ} {M : X.Modules}
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    {U V : X.Opens} (h : V ≤ U) (x : Fin m → ↥Γ(X, U)) :
    finFreeSectionsMap' φ V (X.resPi h m x) =
      M.val.map ((homOfLE h).op : op U ⟶ op V) (finFreeSectionsMap' φ U x) := by
  change ∑ i : Fin m, (X.resPi h m x) i • freeGen φ V i =
    M.val.map ((homOfLE h).op : op U ⟶ op V) (∑ i : Fin m, x i • freeGen φ U i)
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [M.val.map_smul, freeGen_restrict φ h i, Scheme.resPi_apply]
  rfl

/-- The kernel submodules restrict into one another. -/
lemma resPi_mem_kernel {X : Scheme.{u}} {m : ℕ} {M : X.Modules}
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    {U V : X.Opens} (h : V ≤ U) {x : Fin m → ↥Γ(X, U)}
    (hx : finFreeSectionsMap' φ U x = 0) :
    finFreeSectionsMap' φ V (X.resPi h m x) = 0 := by
  rw [finFreeSectionsMap'_resPi φ h x, hx, map_zero]

/-- **The easy half of the localization compatibility**: the span of the restricted kernel is
contained in the kernel. -/
lemma span_resPi_kernel_le {X : Scheme.{u}} {m : ℕ} {M : X.Modules}
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    {U V : X.Opens} (h : V ≤ U) :
    Submodule.span ↥Γ(X, V)
        (X.resPi h m '' (LinearMap.ker (finFreeSectionsMap' φ U) :
          Set (Fin m → ↥Γ(X, U)))) ≤
      LinearMap.ker (finFreeSectionsMap' φ V) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨x, hx, rfl⟩
  exact resPi_mem_kernel φ h hx

/-- The kernel submodule cut out on an open. -/
def kernelSubmodule {X : Scheme.{u}} {m : ℕ} {M : X.Modules}
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M) (U : X.Opens) :
    Submodule ↥Γ(X, U) (Fin m → ↥Γ(X, U)) :=
  LinearMap.ker (finFreeSectionsMap' φ U)

/-- **The hard half of the localization compatibility**: a kernel section over a basic open
`D(f)` of an affine open is a `Γ(X, D(f))`-combination of restricted kernel sections.

Clear denominators — `Γ(X, D(f))` is the localization of `Γ(X, U)` at `f`, so `f ^ k • y`
lifts to some `x` over `U` — and push through the map: `φ_U x` restricts to `0` on `D(f)`.
**This is where quasicoherence of `M` enters**, and it is the only place it is needed: it
says a section vanishing on `D(f)` is annihilated by a power of `f`, so `f ^ l • x` is an
honest kernel section over `U` whose restriction is `f ^ (l + k)` times `y`.  As `f` is a
unit on `D(f)`, `y` is recovered. -/
theorem span_resPi_kernel_ge {X : Scheme.{u}} {m : ℕ} {M : X.Modules} [M.IsQuasicoherent]
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    (U : X.affineOpens) (f : ↥Γ(X, U.1)) :
    kernelSubmodule φ (X.basicOpen f) ≤
      Submodule.span ↥Γ(X, X.basicOpen f)
        (X.resPi (X.basicOpen_le f) m ''
          (kernelSubmodule φ U.1 : Set (Fin m → ↥Γ(X, U.1)))) := by
  letI := U.2.isLocalization_basicOpen f
  intro y hy
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (Submonoid.powers f)
    (Finset.univ : Finset (Fin m)) y
  choose x hx using fun i => hb i (Finset.mem_univ i)
  have hres : X.resPi (X.basicOpen_le f) m x = (b : ↥Γ(X, U.1)) • y := by
    funext i
    rw [Scheme.resPi_apply]
    exact hx i
  have hsmul : ((b : ↥Γ(X, U.1)) • y) =
      (algebraMap ↥Γ(X, U.1) ↥Γ(X, X.basicOpen f) (b : ↥Γ(X, U.1))) • y := rfl
  have h0 : M.val.map ((homOfLE (X.basicOpen_le f)).op) (finFreeSectionsMap' φ U.1 x) = 0 := by
    rw [← finFreeSectionsMap'_resPi φ (X.basicOpen_le f) x, hres, hsmul,
      LinearMap.map_smul, LinearMap.mem_ker.mp hy, smul_zero]
  obtain ⟨l, hl⟩ := Scheme.Modules.exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
    M U.2.isCompact f (finFreeSectionsMap' φ U.1 x) h0
  have hker : f ^ l • x ∈ kernelSubmodule φ U.1 := by
    rw [kernelSubmodule, LinearMap.mem_ker, LinearMap.map_smul]
    exact hl
  have hres2 : X.resPi (X.basicOpen_le f) m (f ^ l • x) =
      (algebraMap ↥Γ(X, U.1) ↥Γ(X, X.basicOpen f) (f ^ l * (b : ↥Γ(X, U.1)))) • y := by
    funext i
    rw [Scheme.resPi_apply]
    change (algebraMap ↥Γ(X, U.1) ↥Γ(X, X.basicOpen f)) (f ^ l * x i) =
      (algebraMap ↥Γ(X, U.1) ↥Γ(X, X.basicOpen f)) (f ^ l * (b : ↥Γ(X, U.1))) * y i
    rw [map_mul, hx i, map_mul, Algebra.smul_def, mul_assoc]
  have hunit : IsUnit (algebraMap ↥Γ(X, U.1) ↥Γ(X, X.basicOpen f)
      ((f : ↥Γ(X, U.1)) ^ l * (b : ↥Γ(X, U.1)))) :=
    IsLocalization.map_units (M := Submonoid.powers f) ↥Γ(X, X.basicOpen f)
      ⟨(f : ↥Γ(X, U.1)) ^ l * (b : ↥Γ(X, U.1)),
        Submonoid.mul_mem _ ⟨l, rfl⟩ b.2⟩
  obtain ⟨u, hu⟩ := hunit
  have hy' : y = (↑u⁻¹ : ↥Γ(X, X.basicOpen f)) •
      X.resPi (X.basicOpen_le f) m (f ^ l • x) := by
    rw [hres2, ← hu, smul_smul, Units.inv_mul, one_smul]
  rw [hy']
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f ^ l • x, hker, rfl⟩)

/-- **The localization compatibility for the kernel**, both halves. -/
theorem span_resPi_kernel {X : Scheme.{u}} {m : ℕ} {M : X.Modules} [M.IsQuasicoherent]
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M)
    (U : X.affineOpens) (f : ↥Γ(X, U.1)) :
    Submodule.span ↥Γ(X, (X.affineBasicOpen f).1)
        (X.resPi (show (X.affineBasicOpen f).1 ≤ U.1 from X.basicOpen_le f) m ''
          (kernelSubmodule φ U.1 : Set (Fin m → ↥Γ(X, U.1)))) =
      kernelSubmodule φ (X.affineBasicOpen f).1 :=
  le_antisymm (span_resPi_kernel_le φ (X.basicOpen_le f)) (span_resPi_kernel_ge φ U f)

/-- **The kernel of a map out of `𝒪^m` into a quasicoherent sheaf, as quasi-coherent
submodule data.**  This is the `S`-point of the Grassmannian attached to `φ`. -/
def kernelSubmoduleSheafData {X : Scheme.{u}} {m : ℕ} {M : X.Modules} [M.IsQuasicoherent]
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M) :
    X.SubmoduleSheafData m where
  submodule U := kernelSubmodule φ U.1
  span_resPi_basicOpen := span_resPi_kernel φ

/-- `finFreeSectionsMap'` **is** `Fintype.linearCombination` against the generating
sections. -/
lemma finFreeSectionsMap'_eq_linearCombination {X : Scheme.{u}} {m : ℕ} {M : X.Modules}
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M) (U : X.Opens) :
    finFreeSectionsMap' φ U = Fintype.linearCombination ↥Γ(X, U) (freeGen φ U) := rfl

/-- **Surjectivity on sections is exactly the span condition** on the generating sections.
This is the form in which the Grassmannian point consumes global generation. -/
lemma surjective_finFreeSectionsMap'_iff {X : Scheme.{u}} {m : ℕ} {M : X.Modules}
    (φ : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin m)) ⟶ M) (U : X.Opens) :
    Function.Surjective (finFreeSectionsMap' φ U) ↔
      Submodule.span ↥Γ(X, U) (Set.range (freeGen φ U)) = ⊤ := by
  rw [← LinearMap.range_eq_top, finFreeSectionsMap'_eq_linearCombination,
    Fintype.range_linearCombination]

end AlgebraicGeometry.Scheme.Modules
