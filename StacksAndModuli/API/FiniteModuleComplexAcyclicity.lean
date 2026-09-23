module

public import StacksAndModuli.API.FiniteFreeComplexHomology
public import StacksAndModuli.API.ModuleExtDepth
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# A depth lemma for finite complexes

This file isolates the homological depth argument used in the finite-module acyclicity
lemma.  For a chain complex of modules, it realizes the concrete cycles, boundaries, and
linear-map homology as three short exact sequences.  Repeated application of the depth
lemma then shows that the homology at a largest possibly nonexact positive degree has
Ext-depth at least one.

The indexing agrees with `Matrix.FiniteFreeComplex.homology`: index `i` refers to homology
at the term in degree `i + 1`.  Thus `linearCycleModule C i` is the kernel of
`C.X (i + 1) ⟶ C.X i`.

The main result is stated first without Noetherian or finiteness hypotheses, since its
proof uses only Ext-vanishing and the depth lemma.  A local Noetherian wrapper records the
hypotheses occurring in the finite-module acyclicity lemma.

Main declarations:

* `ChainComplex.linearCycleStepShortComplex_shortExact`;
* `ChainComplex.linearBoundaryShortComplex_shortExact`;
* `ChainComplex.linearHomologyShortComplex_shortExact`;
* `ChainComplex.extDepthAtLeast_one_linearHomologyModule_of_exact_above`;
* `ChainComplex.extDepthAtLeast_one_linearHomologyModule_of_largest_nonexact`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace ModuleCat

variable {R : Type u} [CommRing R]

namespace ExtDepthAtLeast

/-- A zero module has arbitrary Ext-depth. -/
theorem of_isZero {I : Ideal R} {M : ModuleCat.{u} R} {n : ℕ}
    (hM : IsZero M) : ExtDepthAtLeast I M n := by
  intro i hi
  cases i with
  | zero =>
      apply Ext.addEquiv₀.subsingleton_congr.mpr
      exact ⟨fun f g ↦ hM.eq_of_tgt f g⟩
  | succ i =>
      letI : Injective M := hM.injective
      exact Ext.subsingleton_of_injective _ _ i

/-- A submodule of a module of Ext-depth at least one again has Ext-depth at least one. -/
theorem one_of_mono {I : Ideal R} {M N : ModuleCat.{u} R}
    (f : M ⟶ N) [Mono f] (hN : ExtDepthAtLeast I N 1) :
    ExtDepthAtLeast I M 1 := by
  intro i hi
  have hi₀ : i = 0 := by omega
  subst i
  let _ : Subsingleton (Ext (extDepthTestObject I) N 0) := hN 0 (by omega)
  exact (Ext.postcomp_mk₀_injective_of_mono (extDepthTestObject I) f).subsingleton

end ExtDepthAtLeast

/-- Equal pairs of differentials define equal concrete homology objects in `ModuleCat`.
The proofs that the composites vanish are immaterial by proof irrelevance. -/
theorem of_linearMapHomology_eq_of_eq
    {M N P : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
    {f f' : M →ₗ[R] N} {g g' : N →ₗ[R] P}
    (hf : f = f') (hg : g = g')
    (hgf : g.comp f = 0) (hgf' : g'.comp f' = 0) :
    ModuleCat.of R (LinearMap.Homology f g hgf) =
      ModuleCat.of R (LinearMap.Homology f' g' hgf') := by
  subst f'
  subst g'
  rfl

end ModuleCat

namespace ChainComplex

variable {R : Type u} [CommRing R]

/-- The composite of the two differentials surrounding the term in degree `i + 1`. -/
theorem linearDifferential_comp (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    (C.d (i + 1) i).hom.comp (C.d (i + 2) (i + 1)).hom = 0 := by
  exact congrArg ModuleCat.Hom.hom (C.d_comp_d (i + 2) (i + 1) i)

/-- Concrete cycles at the term in degree `i + 1`. -/
def linearCycleModule (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    ModuleCat.{u} R :=
  ModuleCat.of R (LinearMap.ker (C.d (i + 1) i).hom)

/-- The inclusion of concrete cycles into the term in degree `i + 1`. -/
def linearCycleInclusion (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    C.linearCycleModule i ⟶ C.X (i + 1) :=
  ModuleCat.ofHom (LinearMap.ker (C.d (i + 1) i).hom).subtype

instance mono_linearCycleInclusion (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    Mono (C.linearCycleInclusion i) :=
  (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective

/-- The incoming differential, with codomain restricted to the concrete cycles. -/
def linearBoundaryMap (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    C.X (i + 2) →ₗ[R] LinearMap.ker (C.d (i + 1) i).hom :=
  LinearMap.homologyBoundary
    (C.d (i + 2) (i + 1)).hom (C.d (i + 1) i).hom
    (C.linearDifferential_comp i)

/-- The kernel of the boundary map is the kernel of the incoming differential. -/
@[simp]
theorem ker_linearBoundaryMap (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    LinearMap.ker (C.linearBoundaryMap i) =
      LinearMap.ker (C.d (i + 2) (i + 1)).hom := by
  simpa only [linearBoundaryMap, LinearMap.homologyBoundary,
    LinearMap.ker_codRestrict]

/-- Surjectivity onto cycles is ordinary exactness at the term in degree `i + 1`. -/
theorem surjective_linearBoundaryMap_iff_exact
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    Function.Surjective (C.linearBoundaryMap i) ↔
      Function.Exact (C.d (i + 2) (i + 1)).hom (C.d (i + 1) i).hom := by
  rw [← LinearMap.range_eq_top]
  exact (LinearMap.exact_iff_range_homologyBoundary_eq_top
    (C.d (i + 2) (i + 1)).hom (C.d (i + 1) i).hom
    (C.linearDifferential_comp i)).symm

/-- Concrete boundaries, regarded as a submodule of the concrete cycles. -/
def linearBoundaryModule (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    ModuleCat.{u} R :=
  ModuleCat.of R (LinearMap.range (C.linearBoundaryMap i))

/-- The canonical surjection from the incoming term to the concrete boundaries. -/
def linearBoundaryProjection (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    C.X (i + 2) ⟶ C.linearBoundaryModule i :=
  ModuleCat.ofHom (C.linearBoundaryMap i).rangeRestrict

instance epi_linearBoundaryProjection
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    Epi (C.linearBoundaryProjection i) :=
  (ModuleCat.epi_iff_surjective _).mpr
    (LinearMap.surjective_rangeRestrict (C.linearBoundaryMap i))

/-- The inclusion of concrete boundaries into concrete cycles. -/
def linearBoundaryInclusion (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    C.linearBoundaryModule i ⟶ C.linearCycleModule i :=
  ModuleCat.ofHom (LinearMap.range (C.linearBoundaryMap i)).subtype

instance mono_linearBoundaryInclusion
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    Mono (C.linearBoundaryInclusion i) :=
  (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective

/-- Concrete linear-map homology at the term in degree `i + 1`. -/
def linearHomologyModule (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    ModuleCat.{u} R :=
  ModuleCat.of R <| LinearMap.Homology
    (C.d (i + 2) (i + 1)).hom (C.d (i + 1) i).hom
    (C.linearDifferential_comp i)

/-- The quotient map from concrete cycles to concrete homology. -/
def linearHomologyProjection (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    C.linearCycleModule i ⟶ C.linearHomologyModule i :=
  ModuleCat.ofHom (LinearMap.range (C.linearBoundaryMap i)).mkQ

instance epi_linearHomologyProjection
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    Epi (C.linearHomologyProjection i) :=
  (ModuleCat.epi_iff_surjective _).mpr
    (Submodule.mkQ_surjective (LinearMap.range (C.linearBoundaryMap i)))

/-- The short complex `0 ⟶ Z_(i+1) ⟶ C_(i+2) ⟶ Z_i ⟶ 0`. -/
def linearCycleStepShortComplex
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (X₁ := C.linearCycleModule (i + 1))
    (X₂ := C.X (i + 2))
    (X₃ := C.linearCycleModule i)
    (C.linearCycleInclusion (i + 1))
    (ModuleCat.ofHom (C.linearBoundaryMap i)) (by
      apply ModuleCat.hom_ext
      ext x
      apply Subtype.ext
      exact LinearMap.mem_ker.mp x.property)

/-- The cycle-step short complex is exact in the middle. -/
theorem linearCycleStepShortComplex_exact
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    (C.linearCycleStepShortComplex i).Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range
      (LinearMap.ker (C.d (i + 2) (i + 1)).hom).subtype =
    LinearMap.ker (C.linearBoundaryMap i)
  rw [Submodule.range_subtype, C.ker_linearBoundaryMap i] <;> rfl

/-- Exactness at degree `i + 1` makes the cycle-step sequence short exact. -/
theorem linearCycleStepShortComplex_shortExact
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ)
    (h : Function.Exact
      (C.d (i + 2) (i + 1)).hom (C.d (i + 1) i).hom) :
    (C.linearCycleStepShortComplex i).ShortExact := by
  refine ShortComplex.ShortExact.mk'
    (C.linearCycleStepShortComplex_exact i) ?_ ?_
  · change Mono (C.linearCycleInclusion (i + 1))
    infer_instance
  · change Epi (ModuleCat.ofHom (C.linearBoundaryMap i))
    exact (ModuleCat.epi_iff_surjective _).mpr
      ((C.surjective_linearBoundaryMap_iff_exact i).mpr h)

/-- The short complex `0 ⟶ Z_(i+1) ⟶ C_(i+2) ⟶ B_i ⟶ 0`. -/
def linearBoundaryShortComplex
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (X₁ := C.linearCycleModule (i + 1))
    (X₂ := C.X (i + 2))
    (X₃ := C.linearBoundaryModule i)
    (C.linearCycleInclusion (i + 1))
    (C.linearBoundaryProjection i) (by
      apply ModuleCat.hom_ext
      ext x
      apply Subtype.ext
      apply Subtype.ext
      exact LinearMap.mem_ker.mp x.property)

/-- The cycle-boundary sequence is always short exact. -/
theorem linearBoundaryShortComplex_shortExact
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    (C.linearBoundaryShortComplex i).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range
        (LinearMap.ker (C.d (i + 2) (i + 1)).hom).subtype =
      LinearMap.ker (C.linearBoundaryMap i).rangeRestrict
    rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict,
      C.ker_linearBoundaryMap i] <;> rfl
  · change Mono (C.linearCycleInclusion (i + 1))
    infer_instance
  · change Epi (C.linearBoundaryProjection i)
    infer_instance

/-- The short complex `0 ⟶ B_i ⟶ Z_i ⟶ H_i ⟶ 0`. -/
def linearHomologyShortComplex
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk
    (X₁ := C.linearBoundaryModule i)
    (X₂ := C.linearCycleModule i)
    (X₃ := C.linearHomologyModule i)
    (C.linearBoundaryInclusion i)
    (C.linearHomologyProjection i) (by
      apply ModuleCat.hom_ext
      ext x
      exact (Submodule.Quotient.mk_eq_zero _).mpr x.property)

/-- The boundary-cycle-homology sequence is short exact. -/
theorem linearHomologyShortComplex_shortExact
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    (C.linearHomologyShortComplex i).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range
        (LinearMap.range (C.linearBoundaryMap i)).subtype =
      LinearMap.ker (LinearMap.range (C.linearBoundaryMap i)).mkQ
    rw [Submodule.range_subtype, Submodule.ker_mkQ] <;> rfl
  · change Mono (C.linearBoundaryInclusion i)
    infer_instance
  · change Epi (C.linearHomologyProjection i)
    infer_instance

/-- If the source above a degree is zero and the complex is exact there, its cycle module
in that degree is zero. -/
theorem isZero_linearCycleModule_of_exact_of_isZero_source
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ)
    (hzero : IsZero (C.X (i + 2)))
    (hexact : Function.Exact
      (C.d (i + 2) (i + 1)).hom (C.d (i + 1) i).hom) :
    IsZero (C.linearCycleModule i) := by
  have hS := C.linearCycleStepShortComplex_shortExact i hexact
  letI : Epi (C.linearCycleStepShortComplex i).g := hS.epi_g
  exact IsZero.of_epi (C.linearCycleStepShortComplex i).g hzero

/-- If the source of a boundary map is zero, its boundary module is zero. -/
theorem isZero_linearBoundaryModule_of_isZero_source
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ)
    (hzero : IsZero (C.X (i + 2))) :
    IsZero (C.linearBoundaryModule i) := by
  have hS := C.linearBoundaryShortComplex_shortExact i
  letI : Epi (C.linearBoundaryShortComplex i).g := hS.epi_g
  exact IsZero.of_epi (C.linearBoundaryShortComplex i).g hzero

/-- Ext-depth form of the finite-complex acyclicity depth argument.

The term in degree `N + 1` is the last possibly nonzero term.  If all homology indices
strictly above `n` are exact and the term in degree `j` has Ext-depth at least `j`, then
the homology at degree `n + 1` has Ext-depth at least one. -/
theorem extDepthAtLeast_one_linearHomologyModule_of_exact_above
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (I : Ideal R) {n N : ℕ}
    (hnN : n ≤ N) (hzero : IsZero (C.X (N + 2)))
    (hdepth : ∀ j : ℕ, j ≤ N + 1 → ModuleCat.ExtDepthAtLeast I (C.X j) j)
    (hexact : ∀ j : ℕ, n < j → j ≤ N →
      Function.Exact
        (C.d (j + 2) (j + 1)).hom (C.d (j + 1) j).hom) :
    ModuleCat.ExtDepthAtLeast I (C.linearHomologyModule n) 1 := by
  have hcycle : ModuleCat.ExtDepthAtLeast I (C.linearCycleModule n) 1 := by
    apply ModuleCat.ExtDepthAtLeast.one_of_mono (C.linearCycleInclusion n)
    exact (hdepth (n + 1) (by omega)).of_le (by omega)
  have hboundary : ModuleCat.ExtDepthAtLeast I (C.linearBoundaryModule n) 2 := by
    rcases eq_or_lt_of_le hnN with hnN' | hnN'
    · subst n
      exact ModuleCat.ExtDepthAtLeast.of_isZero
        (C.isZero_linearBoundaryModule_of_isZero_source N hzero)
    · have htopZero : IsZero (C.linearCycleModule N) :=
        C.isZero_linearCycleModule_of_exact_of_isZero_source N hzero
          (hexact N hnN' le_rfl)
      have htopDepth :
          ModuleCat.ExtDepthAtLeast I (C.linearCycleModule N) (N + 2) :=
        ModuleCat.ExtDepthAtLeast.of_isZero htopZero
      have hnext :
          ModuleCat.ExtDepthAtLeast I (C.linearCycleModule (n + 1)) (n + 3) := by
        apply Nat.decreasingInduction' (n := N) (m := n + 1)
          (P := fun j ↦
            ModuleCat.ExtDepthAtLeast I (C.linearCycleModule j) (j + 2))
        · intro j hjN hnj ih
          have hleft : ModuleCat.ExtDepthAtLeast I
              (C.linearCycleModule (j + 1)) ((j + 2) + 1) := by
            convert ih using 1 <;> omega
          exact ModuleCat.ExtDepthAtLeast.shortExact_right
            (C.linearCycleStepShortComplex_shortExact j
              (hexact j (by omega) (by omega)))
            (hdepth (j + 2) (by omega)) hleft
        · omega
        · exact htopDepth
      have hleft : ModuleCat.ExtDepthAtLeast I
          (C.linearCycleModule (n + 1)) ((n + 2) + 1) := by
        convert hnext using 1 <;> omega
      have hb := ModuleCat.ExtDepthAtLeast.shortExact_right
        (C.linearBoundaryShortComplex_shortExact n)
        (hdepth (n + 2) (by omega)) hleft
      exact hb.of_le (by omega)
  exact ModuleCat.ExtDepthAtLeast.shortExact_right
    (C.linearHomologyShortComplex_shortExact n) hcycle hboundary

/-- Local Noetherian finite-module form: the homology at a largest nonexact positive
degree has depth at least one, expressed by Ext-vanishing against the residue field. -/
theorem extDepthAtLeast_one_linearHomologyModule_of_largest_nonexact
    [IsNoetherianRing R] [IsLocalRing R]
    (C : ChainComplex (ModuleCat.{u} R) ℕ) {n N : ℕ}
    (hfinite : ∀ j : ℕ, Module.Finite R (C.X j))
    (hnN : n ≤ N) (hzero : IsZero (C.X (N + 2)))
    (hdepth : ∀ j : ℕ, j ≤ N + 1 →
      ModuleCat.ExtDepthAtLeast (IsLocalRing.maximalIdeal R) (C.X j) j)
    (hnotExact : ¬ Function.Exact
      (C.d (n + 2) (n + 1)).hom (C.d (n + 1) n).hom)
    (hexact : ∀ j : ℕ, n < j → j ≤ N →
      Function.Exact
        (C.d (j + 2) (j + 1)).hom (C.d (j + 1) j).hom) :
    ModuleCat.ExtDepthAtLeast (IsLocalRing.maximalIdeal R)
      (C.linearHomologyModule n) 1 := by
  clear hfinite hnotExact
  exact C.extDepthAtLeast_one_linearHomologyModule_of_exact_above
    (IsLocalRing.maximalIdeal R) hnN hzero hdepth hexact

end ChainComplex

namespace Matrix.FiniteFreeComplex

variable {R : Type u} [CommRing R]

/-- Matrix-complex specialization of the Ext-depth acyclicity argument. -/
theorem extDepthAtLeast_one_homology_of_exact_above
    (C : FiniteFreeComplex R) (I : Ideal R) {n N : ℕ}
    (hnN : n ≤ N) (hzero : C.termRank (N + 2) = 0)
    (hdepth : ∀ j : ℕ, j ≤ N + 1 →
      ModuleCat.ExtDepthAtLeast I (C.toChainComplex.X j) j)
    (hexact : ∀ j : ℕ, n < j → j ≤ N →
      Function.Exact
        (Matrix.toLin' (C.differential (j + 1)))
        (Matrix.toLin' (C.differential j))) :
    ModuleCat.ExtDepthAtLeast I (ModuleCat.of R (C.homology n)) 1 := by
  have hzero' : IsZero (C.toChainComplex.X (N + 2)) := by
    change IsZero (ModuleCat.of R (Fin (C.termRank (N + 2)) → R))
    letI : Subsingleton (Fin (C.termRank (N + 2)) → R) := by
      rw [hzero]
      infer_instance
    exact ModuleCat.isZero_of_subsingleton _
  have h := C.toChainComplex.extDepthAtLeast_one_linearHomologyModule_of_exact_above
    I hnN hzero' hdepth (fun j hnj hjN ↦ by
      have hIncoming :
          (C.toChainComplex.d (j + 2) (j + 1)).hom =
            Matrix.toLin' (C.differential (j + 1)) := by
        simpa only [Nat.add_assoc] using C.toChainComplex_d (j + 1)
      have hOutgoing :
          (C.toChainComplex.d (j + 1) j).hom =
            Matrix.toLin' (C.differential j) :=
        C.toChainComplex_d j
      rw [hIncoming, hOutgoing]
      exact hexact j hnj hjN)
  have hIncoming :
      (C.toChainComplex.d (n + 2) (n + 1)).hom =
        Matrix.toLin' (C.differential (n + 1)) := by
    simpa only [Nat.add_assoc] using C.toChainComplex_d (n + 1)
  have hOutgoing :
      (C.toChainComplex.d (n + 1) n).hom =
        Matrix.toLin' (C.differential n) :=
    C.toChainComplex_d n
  have hHomology : C.toChainComplex.linearHomologyModule n =
      ModuleCat.of R (LinearMap.Homology
        (Matrix.toLin' (C.differential (n + 1)))
        (Matrix.toLin' (C.differential n)) (C.differential_comp n)) := by
    unfold ChainComplex.linearHomologyModule
    exact ModuleCat.of_linearMapHomology_eq_of_eq hIncoming hOutgoing
      (C.toChainComplex.linearDifferential_comp n) (C.differential_comp n)
  change ModuleCat.ExtDepthAtLeast I (ModuleCat.of R (LinearMap.Homology
    (Matrix.toLin' (C.differential (n + 1)))
    (Matrix.toLin' (C.differential n)) (C.differential_comp n))) 1
  exact hHomology ▸ h

end Matrix.FiniteFreeComplex

end
