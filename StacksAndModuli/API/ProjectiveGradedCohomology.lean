module

public import StacksAndModuli.API.ProjectiveGradedModule
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Cohomology of quasi-coherent sheaves on projective space, in the graded-module model

Supporting API with no Stacks Project counterpart, developed for §2.3 (Castelnuovo–Mumford
regularity) of *Stacks and Moduli*.

`StacksAndModuli/API/ProjectiveGradedModule.lean` models a quasi-coherent sheaf on `ℙⁿ_k` by a
`ℤ`-graded module over `S = k[x₀, …, x_n]`. This file adds the cohomology.

Mathlib has no directly computable *coherent-sheaf* cohomology on projective space. Abstract
sheaf cohomology does exist —
`CategoryTheory.Sheaf.H` is `Ext` from the constant sheaf `ℤ`, and
`StacksAndModuli/API/SheafCohomologyModule.lean`, `…/SheafCohomologyModuleLES.lean` and
`…/FlasqueVanishing.lean` add the module structure over `Γ(X, 𝒪_X)`, the long exact
sequence with linear maps, additivity of `χ`, and the vanishing of `Hⁿ⁺¹` on a flasque
sheaf. This foundational file instead *packages* the additional projective-space structure
needed by the arguments of §2.3 as `Cohomology k`: a graded-module model, its Čech
cohomology, Serre vanishing, coherence, and finiteness. The canonical Čech term is constructed
downstream in `StacksAndModuli/API/ProjectiveGradedCohomologyExists.lean`; separating the interface
here keeps the regularity arguments independent of that construction. See
`StacksAndModuli/Section2.3-Regularity/COMMENTARY.md`.

`Cohomology.Hgr M i` is the *graded* module `⨁_d Hⁱ(ℙⁿ, M~(d))`, so that the multiplication
maps `Hⁱ(M~(d)) ⊗ S_e → Hⁱ(M~(d+e))` of Castelnuovo's theorem are part of the data, and
`Cohomology.H M i d = Hⁱ(ℙⁿ, M~(d))`.

Not every standard fact is a field. Two are *proved* from the others: the additivity of the
Euler characteristic in short exact sequences (`Cohomology.chi_add`), by rank–nullity along the
long exact sequence and a telescoping alternating sum; and the value
`h⁰(ℙⁿ, 𝒪(d)) = C(n+d, n)` (`Cohomology.finrank_HgrZero_structureModule`), from the
identification of `H⁰(𝒪(d))` with the forms of degree `d` and the stars-and-bars count of
`StacksAndModuli/API/HomogeneousDimension.lean`.

Main declarations:
- `AlgebraicGeometry.ProjectiveSpace.Cohomology`: the packaged cohomology theory.
- `AlgebraicGeometry.ProjectiveSpace.Cohomology.chi_add`,
  `AlgebraicGeometry.ProjectiveSpace.Cohomology.finrank_HgrZero_structureModule`: two standard
  facts derived from the other fields rather than assumed.
- `AlgebraicGeometry.ProjectiveSpace.Cohomology.H`, `.h`: the cohomology groups and their
  dimensions.
- `AlgebraicGeometry.ProjectiveSpace.Cohomology.BaseChange`: flat base change along a field
  extension.
- `AlgebraicGeometry.ProjectiveSpace.Cohomology.BaseChange.refl`, `.comp`: identity and
  composition of packaged base changes.
- `AlgebraicGeometry.ProjectiveSpace.Cohomology.exists_infinite_field_extension`: the explicit
  infinite extension `k(t)`; only its cohomological comparison remains an obligation.
- `AlgebraicGeometry.ProjectiveSpace.Cohomology.HasInfiniteBaseChange`: the comparison
  hypothesis used to reduce arguments to an infinite field.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open CategoryTheory GradedModule

/-- The cohomology of quasi-coherent sheaves on the projective spaces `ℙⁿ_k`, in the
graded-module model of `GradedModule`, packaged together with the standard properties used in
§2.3 of *Stacks and Moduli*.

`Hgr M i` is the graded `S`-module `⨁_d Hⁱ(ℙⁿ, M~(d))`; its degree-`d` piece `H M i d` is
`Hⁱ(ℙⁿ, M~(d))`, and its multiplication maps are the ones appearing in Castelnuovo's theorem
(Proposition 2.3.5(2)).

Each field is a standard theorem; the references are Hartshorne III.5 and Stacks 01XS, 0B5U,
02O5. The canonical term of this structure is the graded Čech theory constructed in
`ProjectiveGradedCohomologyExists.lean`. -/
structure Cohomology (k : Type u) [Field k] where
  /-- `Hgr M i` is the graded module `⨁_d Hⁱ(ℙⁿ, M~(d))`. -/
  Hgr : ∀ {n : ℕ}, GradedModule k n → ℕ → GradedModule k n
  /-- Cohomology is a functor. -/
  map : ∀ {n : ℕ} {M N : GradedModule k n}, (M ⟶ N) → ∀ i : ℕ, Hgr M i ⟶ Hgr N i
  /-- Functoriality: identities. -/
  map_id : ∀ {n : ℕ} (M : GradedModule k n) (i : ℕ), map (𝟙 M) i = 𝟙 _
  /-- Functoriality: composition. -/
  map_comp : ∀ {n : ℕ} {M N P : GradedModule k n} (f : M ⟶ N) (g : N ⟶ P) (i : ℕ),
    map (f ≫ g) i = map f i ≫ map g i
  /-- The connecting homomorphism of the long exact cohomology sequence. -/
  δ : ∀ {n : ℕ} {M N P : GradedModule k n} {f : M ⟶ N} {g : N ⟶ P},
    ShortExact f g → ∀ (i : ℕ) (d : ℤ), (Hgr P i).obj d ⟶ (Hgr M (i + 1)).obj d
  /-- `H⁰` of a short exact sequence is left exact. -/
  injective_map_zero : ∀ {n : ℕ} {M N P : GradedModule k n} {f : M ⟶ N} {g : N ⟶ P}
    (_ : ShortExact f g) (d : ℤ), Function.Injective ((map f 0).app d).hom
  /-- Exactness of the long exact sequence at `Hⁱ(N)`. -/
  exact_map_map : ∀ {n : ℕ} {M N P : GradedModule k n} {f : M ⟶ N} {g : N ⟶ P}
    (_ : ShortExact f g) (i : ℕ) (d : ℤ),
    Function.Exact ((map f i).app d).hom ((map g i).app d).hom
  /-- Exactness of the long exact sequence at `Hⁱ(P)`. -/
  exact_map_δ : ∀ {n : ℕ} {M N P : GradedModule k n} {f : M ⟶ N} {g : N ⟶ P}
    (hfg : ShortExact f g) (i : ℕ) (d : ℤ),
    Function.Exact ((map g i).app d).hom (δ hfg i d).hom
  /-- Exactness of the long exact sequence at `Hⁱ⁺¹(M)`. -/
  exact_δ_map : ∀ {n : ℕ} {M N P : GradedModule k n} {f : M ⟶ N} {g : N ⟶ P}
    (hfg : ShortExact f g) (i : ℕ) (d : ℤ),
    Function.Exact (δ hfg i d).hom ((map f (i + 1)).app d).hom
  /-- Grothendieck vanishing: cohomology vanishes above the dimension. -/
  subsingleton_of_lt : ∀ {n : ℕ} (M : GradedModule k n) (i : ℕ) (d : ℤ), n < i →
    Subsingleton ((Hgr M i).obj d)
  /-- Cohomology of a twist is the shift of the cohomology: `Hⁱ(M(a)~(d)) = Hⁱ(M~(d+a))`. -/
  twistIso : ∀ {n : ℕ} (M : GradedModule k n) (a : ℤ) (i : ℕ) (d : ℤ),
    (Hgr (M.twist a) i).obj d ≅ (Hgr M i).obj (d + a)
  /-- Coherence of a quasi-coherent sheaf, i.e. finite generation of the graded module up to
  torsion. -/
  IsCoherent : ∀ {n : ℕ}, GradedModule k n → Prop
  /-- Cohomology is insensitive to the closed immersion of a hyperplane: if `N` is killed by
  the linear form `L = ∑ cᵢxᵢ` whose `j`-th coefficient is a unit, then `N` is (the pushforward
  of) a sheaf on `H = V(L) ≅ ℙⁿ`, and its cohomology there agrees with its cohomology on
  `ℙⁿ⁺¹`. -/
  dropVarIso : ∀ {n : ℕ} (N : GradedModule k (n + 1)) (c : Fin (n + 2) → k) (j : Fin (n + 2)),
    IsUnit (c j) → (∀ d e (h : d + 1 = e), N.mulL c d e h = 0) →
    IsCoherent (N.dropVar j) → ∀ i : ℕ,
    Hgr (N.dropVar j) i ≅ (Hgr N i).dropVar j
  /-- The structure sheaf is coherent. -/
  isCoherent_structureModule : ∀ {n : ℕ}, IsCoherent (structureModule k n)
  /-- Twists of coherent sheaves are coherent. -/
  isCoherent_twist : ∀ {n : ℕ} {M : GradedModule k n}, IsCoherent M → ∀ a : ℤ,
    IsCoherent (M.twist a)
  /-- Finite direct sums of coherent sheaves are coherent. -/
  isCoherent_pow : ∀ {n : ℕ} {M : GradedModule k n}, IsCoherent M → ∀ r : ℕ, IsCoherent (M.pow r)
  /-- Cokernels of maps of coherent sheaves are coherent. -/
  isCoherent_coker : ∀ {n : ℕ} {M N : GradedModule k n} (f : M ⟶ N),
    IsCoherent M → IsCoherent N → IsCoherent (coker f)
  /-- Subsheaves of coherent sheaves are coherent (`ℙⁿ` is noetherian). -/
  isCoherent_of_injective : ∀ {n : ℕ} {M N : GradedModule k n} (f : M ⟶ N),
    (∀ d, Function.Injective (f.app d).hom) → IsCoherent N → IsCoherent M
  /-- A coherent sheaf **killed by a linear form** whose `j`-th coefficient is a unit is
  coherent on the hyperplane.

  The hypothesis is necessary, not cosmetic: `k[x₀, x₁]` is coherent on `ℙ¹`, but forgetting
  the action of `x₁` leaves a module over `k[x₀]` whose degree-`d` piece has dimension `d+1`,
  which is not finitely generated.  Without it this field is false, and (with
  `serre_vanishing`) makes the structure empty.  It is only ever used through
  `isCoherent_restrictL`, where `M.quotL c` is killed by `L` by construction. -/
  isCoherent_dropVar : ∀ {n : ℕ} {N : GradedModule k (n + 1)}, IsCoherent N →
    ∀ (c : Fin (n + 2) → k) (j : Fin (n + 2)), IsUnit (c j) →
    (∀ d e (h : d + 1 = e), N.mulL c d e h = 0) → IsCoherent (N.dropVar j)
  /-- Cohomology of a coherent sheaf is finite dimensional. -/
  finiteDimensional : ∀ {n : ℕ} {M : GradedModule k n}, IsCoherent M → ∀ (i : ℕ) (d : ℤ),
    FiniteDimensional k ((Hgr M i).obj d)
  /-- Serre vanishing: the higher cohomology of a coherent sheaf vanishes after a large
  twist. -/
  serre_vanishing : ∀ {n : ℕ} {M : GradedModule k n}, IsCoherent M → ∀ i : ℕ, 1 ≤ i →
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → Subsingleton ((Hgr M i).obj d)
  /-- A graded module with **no irrelevant torsion**, i.e. `H⁰_m(M) = 0`: no nonzero element
  is killed by a power of every variable.

  This is the hypothesis under which a general hyperplane is a nonzerodivisor.  It cannot be
  dropped: a module of finite length has no nonzerodivisor at all, while being invisible to
  `Hgr` (all its localizations vanish).  Omitting it made this structure empty — see
  `StacksAndModuli/API/CohomologyInterfaceObstruction.lean` and this section's COMMENTARY. -/
  NoIrrelevantTorsion : ∀ {n : ℕ}, GradedModule k n → Prop
  /-- Finite direct sums of the structure sheaf have no irrelevant torsion. -/
  noIrrelevantTorsion_pow_structureModule : ∀ {n : ℕ} (r : ℕ),
    NoIrrelevantTorsion ((structureModule k n).pow r)
  /-- **Every coherent sheaf has a torsion-free model with the same cohomology**, namely the
  quotient `M/H⁰_m(M)` by the irrelevant torsion.  It is a quotient, hence coherent; it is an
  isomorphism in all large degrees, because the irrelevant torsion of a finitely generated
  module has finite length; and it changes no cohomology, because a finite-length module has
  all its localizations zero. -/
  exists_noIrrelevantTorsion_quotient : ∀ {n : ℕ} {M : GradedModule k n}, IsCoherent M →
    ∃ (N : GradedModule k n) (φ : M ⟶ N), IsCoherent N ∧ NoIrrelevantTorsion N ∧
      (∀ d, Function.Surjective (φ.app d).hom) ∧
      (∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → Function.Injective (φ.app d).hom) ∧
      (∀ (i : ℕ) (d : ℤ), Function.Bijective ((map φ i).app d).hom)
  /-- A graded module vanishing in all large degrees has finite length, so its sheaf is zero
  and it has no cohomology. -/
  subsingleton_Hgr_of_eventually_zero : ∀ {n : ℕ} {M : GradedModule k n},
    (∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → Subsingleton (M.obj d)) →
    ∀ (i : ℕ) (d : ℤ), Subsingleton ((Hgr M i).obj d)
  /-- Over an infinite field, a coherent sheaf **with no irrelevant torsion** admits a
  hyperplane avoiding its associated points: a linear form `L = ∑ cᵢxᵢ` with some coefficient
  a unit which is a nonzerodivisor on the sheaf.  The torsion hypothesis is essential; see
  `NoIrrelevantTorsion`. -/
  exists_nonZeroDivisor_linearForm : ∀ {n : ℕ}, Infinite k → ∀ M M' : GradedModule k (n + 1),
    IsCoherent M → IsCoherent M' → NoIrrelevantTorsion M → NoIrrelevantTorsion M' →
    ∃ (c : Fin (n + 2) → k) (j : Fin (n + 2)), IsUnit (c j) ∧
      (∀ d, Function.Injective ((M.mulLHom c).app d).hom) ∧
      (∀ d, Function.Injective ((M'.mulLHom c).app d).hom)
  /-- `H⁰(ℙⁿ, 𝒪(d)) = S_d` **in nonnegative degrees**: the global sections of the twisting
  sheaves are the graded pieces of the polynomial ring.

  The restriction to `d ≥ 0` is necessary, not cosmetic: on `ℙ⁰ = Spec k` every `𝒪(d)` is
  trivial, so `H⁰(ℙ⁰, 𝒪(d)) = k` for all `d`, whereas `S_d = 0` for `d < 0`.  Asserting the
  isomorphism in all degrees for all `n` makes this structure empty — it contradicts
  `mulSpan_zero` at `n = 0`.  See `StacksAndModuli/Section2.3-Regularity/COMMENTARY.md`. -/
  hgrZeroStructureIso : ∀ {n : ℕ} (d : ℤ), 0 ≤ d →
    ((Hgr (structureModule k n) 0).obj d ≅ (structureModule k n).obj d)
  /-- The higher cohomology of `𝒪(d)` vanishes except in the top degree, where it vanishes for
  `d ≥ -n`. -/
  subsingleton_Hgr_structureModule : ∀ {n : ℕ} (i : ℕ) (d : ℤ), 1 ≤ i →
    (i ≠ n ∨ -(n : ℤ) ≤ d) → Subsingleton ((Hgr (structureModule k n) i).obj d)
  /-- `H⁰` and, more generally, `Hⁱ` take the multiplication map `L : M(-1) → M` of a linear
  form to multiplication by that linear form on the graded cohomology module. -/
  map_mulLHom : ∀ {n : ℕ} (M : GradedModule k n) (c : Fin (n + 1) → k) (i : ℕ) (d : ℤ),
    (twistIso M (-1) i d).inv ≫ (map (M.mulLHom c) i).app d
      = (Hgr M i).mulL c (d + -1) d (by ring)
  /-- On `ℙ⁰ = Spec k` the multiplication maps `H⁰(F(d)) ⊗ S_e → H⁰(F(d+e))` are surjective:
  multiplication by the unique variable is an isomorphism on global sections. This is the base
  case `n = 0` of the induction in Proposition 2.3.5(2). -/
  mulSpan_zero : ∀ (M : GradedModule k 0) (d e : ℤ), d ≤ e → (Hgr M 0).mulSpan d e = ⊤
  /-- On `ℙ⁰ = Spec k` multiplication by the variable is invertible on all of the cohomology:
  every `𝒪(d)` is trivial on a point.  Together with `mulSpan_zero` this makes the
  cohomology of a sheaf on `ℙ⁰` independent of the twist, which is the base case of
  Snapper's theorem (`Cohomology.exists_hasHilbertPolynomial`). -/
  zero_mulX_bijective : ∀ (M : GradedModule k 0) (i : Fin 1) (q : ℕ) (d : ℤ),
    Function.Bijective (((Hgr M q).mulX i d).hom)
  /-- Cohomology commutes with finite direct sums. -/
  HgrPowIso : ∀ {n : ℕ} (M : GradedModule k n) (r : ℕ) (i : ℕ) (d : ℤ),
    (Hgr (M.pow r) i).obj d ≅ ((Hgr M i).pow r).obj d
  /-- Global generation of `M~(d)`, i.e. surjectivity of `H⁰(ℙⁿ, M~(d)) ⊗ 𝒪 → M~(d)`. -/
  IsGloballyGenerated : ∀ {n : ℕ}, GradedModule k n → ℤ → Prop
  /-- A coherent sheaf is globally generated in degree `d` exactly when the multiplication maps
  `H⁰(M~(d)) ⊗ S_e → H⁰(M~(d+e))` are surjective for all large `e`; this is the criterion by
  which Proposition 2.3.5(3) is verified. -/
  isGloballyGenerated_iff : ∀ {n : ℕ} {M : GradedModule k n}, IsCoherent M → ∀ d : ℤ,
    (IsGloballyGenerated M d ↔ ∃ e₀ : ℤ, ∀ e : ℤ, e₀ ≤ e →
      (Hgr M 0).mulSpan d e = ⊤)

namespace Cohomology

variable {k : Type u} [Field k] (C : Cohomology k)

/-- `Hⁱ(ℙⁿ, M~(d))`, the `i`-th cohomology of the `d`-th twist of the sheaf modelled by `M`. -/
def H {n : ℕ} (M : GradedModule k n) (i : ℕ) (d : ℤ) : ModuleCat.{u} k := (C.Hgr M i).obj d

@[simp] lemma H_def {n : ℕ} (M : GradedModule k n) (i : ℕ) (d : ℤ) :
    C.H M i d = (C.Hgr M i).obj d := rfl

/-- `hⁱ(ℙⁿ, M~(d)) = dim_k Hⁱ(ℙⁿ, M~(d))`. -/
noncomputable def h {n : ℕ} (M : GradedModule k n) (i : ℕ) (d : ℤ) : ℕ :=
  Module.finrank k (C.H M i d)

/-- A subsingleton cohomology module has dimension zero. -/
lemma h_eq_zero_of_subsingleton {n : ℕ} {M : GradedModule k n} {i : ℕ} {d : ℤ}
    (hs : Subsingleton ((C.Hgr M i).obj d)) : C.h M i d = 0 := by
  have : Subsingleton (C.H M i d) := hs
  simp [h, Module.finrank_eq_zero_of_subsingleton]

/-- A coherent sheaf whose `i`-th cohomology has dimension zero in degree `d` has vanishing
`i`-th cohomology there. -/
lemma subsingleton_of_h_eq_zero {n : ℕ} {M : GradedModule k n} (hM : C.IsCoherent M) (i : ℕ)
    (d : ℤ) (hz : C.h M i d = 0) : Subsingleton ((C.Hgr M i).obj d) := by
  have hfd : FiniteDimensional k (C.H M i d) := C.finiteDimensional hM i d
  have hall : ∀ x : (C.H M i d), x = 0 := finrank_zero_iff_forall_zero.mp hz
  exact ⟨fun x y => by rw [hall x, hall y]⟩

/-- The Euler characteristic `χ(M~(d)) = ∑ᵢ (-1)ⁱ hⁱ(ℙⁿ, M~(d))`; the sum is finite because
cohomology vanishes above the dimension `n`. -/
noncomputable def chi {n : ℕ} (M : GradedModule k n) (d : ℤ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (C.h M i d : ℤ)

/-- `M` has Hilbert polynomial `P` if `χ(M~(d)) = P(d)` for every `d`. -/
def HasHilbertPolynomial {n : ℕ} (M : GradedModule k n) (P : Polynomial ℚ) : Prop :=
  ∀ d : ℤ, (C.chi M d : ℚ) = P.eval (d : ℚ)

/-- Cohomological dimensions transport along a comparison map that is bijective in every
cohomological degree. -/
lemma h_congr {n : ℕ} {M N : GradedModule k n} (φ : M ⟶ N)
    (hφ : ∀ (i : ℕ) (d : ℤ), Function.Bijective ((C.map φ i).app d).hom) (i : ℕ) (d : ℤ) :
    C.h M i d = C.h N i d :=
  (LinearEquiv.ofBijective ((C.map φ i).app d).hom (hφ i d)).finrank_eq

/-- Euler characteristics agree under a comparison that is bijective in every
cohomological degree. -/
lemma chi_congr {n : ℕ} {M N : GradedModule k n} (φ : M ⟶ N)
    (hφ : ∀ (i : ℕ) (d : ℤ), Function.Bijective ((C.map φ i).app d).hom) (d : ℤ) :
    C.chi M d = C.chi N d :=
  Finset.sum_congr rfl fun i _ => by rw [C.h_congr φ hφ i d]

/-- Hilbert polynomials are cohomological, so they transport along the quotient of a coherent
sheaf by its irrelevant torsion. -/
lemma hasHilbertPolynomial_congr {n : ℕ} {M N : GradedModule k n} (φ : M ⟶ N)
    (hφ : ∀ (i : ℕ) (d : ℤ), Function.Bijective ((C.map φ i).app d).hom) (P : Polynomial ℚ) :
    C.HasHilbertPolynomial M P ↔ C.HasHilbertPolynomial N P := by
  constructor
  · exact fun hP d => by rw [← C.chi_congr φ hφ d]; exact hP d
  · exact fun hP d => by rw [C.chi_congr φ hφ d]; exact hP d

/-- Vanishing of the cohomology of `F|_H` on `H ≅ ℙⁿ` is the same as vanishing of the
cohomology of its pushforward `M/LM` on `ℙⁿ⁺¹`. -/
lemma subsingleton_Hgr_restrictL_iff {n : ℕ} (M : GradedModule k (n + 1)) (c : Fin (n + 2) → k)
    (j : Fin (n + 2)) (hj : IsUnit (c j)) (hcoh : C.IsCoherent (M.restrictL c j))
    (i : ℕ) (d : ℤ) :
    Subsingleton ((C.Hgr (M.restrictL c j) i).obj d) ↔
      Subsingleton ((C.Hgr (M.quotL c) i).obj d) := by
  have hkill : ∀ (a b : ℤ) (h : a + 1 = b), (M.quotL c).mulL c a b h = 0 :=
    fun a b h => quotL_mulL_eq_zero M c a b h
  have e := isoApp (C.dropVarIso (M.quotL c) c j hj hkill hcoh i) d
  refine ⟨fun hs => ?_, fun hs => ?_⟩
  · have : Subsingleton ((C.Hgr ((M.quotL c).dropVar j) i).obj d) := hs
    exact e.symm.toLinearEquiv.toEquiv.subsingleton
  · have : Subsingleton (((C.Hgr (M.quotL c) i).dropVar j).obj d) := hs
    exact e.toLinearEquiv.toEquiv.subsingleton

/-- The graded cohomology of `F|_H` on `H ≅ ℙⁿ` is the restriction of the graded cohomology of
its pushforward. -/
lemma mulSpan_Hgr_restrictL_le {n : ℕ} (M : GradedModule k (n + 1)) (c : Fin (n + 2) → k)
    (j : Fin (n + 2)) (hj : IsUnit (c j)) (hcoh : C.IsCoherent (M.restrictL c j))
    (i : ℕ) (d e : ℤ)
    (h : (C.Hgr (M.restrictL c j) i).mulSpan d e = ⊤) :
    (C.Hgr (M.quotL c) i).mulSpan d e = ⊤ := by
  have hkill : ∀ (a b : ℤ) (hab : a + 1 = b), (M.quotL c).mulL c a b hab = 0 :=
    fun a b hab => quotL_mulL_eq_zero M c a b hab
  have hiso := C.dropVarIso (M.quotL c) c j hj hkill hcoh i
  have h2 : ((C.Hgr (M.quotL c) i).dropVar j).mulSpan d e = ⊤ :=
    mulSpan_eq_top_of_iso hiso d e h
  exact eq_top_iff.mpr (h2 ▸ dropVar_mulSpan_le (C.Hgr (M.quotL c) i) j d e)

/-- **If the third term of a short exact sequence has no cohomology, the first map is an
isomorphism on cohomology in every degree.**  This is just the long exact sequence, and it is
what lets a comparison map with finite-length kernel and cokernel be treated as an
isomorphism: a finite-length graded module has all its localizations zero, hence no
cohomology. -/
lemma bijective_map_of_shortExact_of_subsingleton {n : ℕ} {M N P : GradedModule k n}
    {u : M ⟶ N} {v : N ⟶ P} (hSE : ShortExact u v)
    (hP : ∀ (i : ℕ) (d : ℤ), Subsingleton ((C.Hgr P i).obj d)) (i : ℕ) (d : ℤ) :
    Function.Bijective ((C.map u i).app d).hom := by
  refine ⟨?_, ?_⟩
  · cases i with
    | zero => exact C.injective_map_zero hSE d
    | succ i =>
        intro x y hxy
        have h0 : ((C.map u (i + 1)).app d).hom (x - y) = 0 := by
          rw [map_sub, hxy, sub_self]
        obtain ⟨z, hz⟩ := (C.exact_δ_map hSE i d _).mp h0
        haveI := hP i d
        rw [Subsingleton.elim z 0, map_zero] at hz
        exact sub_eq_zero.mp hz.symm
  · intro z
    haveI := hP i d
    exact (C.exact_map_map hSE i d _).mp (Subsingleton.elim _ _)

/-- Coherence is preserved by restriction to a hyperplane. -/
lemma isCoherent_quotL {n : ℕ} {M : GradedModule k n} (hM : C.IsCoherent M)
    (c : Fin (n + 1) → k) : C.IsCoherent (M.quotL c) :=
  C.isCoherent_coker _ (C.isCoherent_twist hM (-1)) hM

/-- Coherence is preserved by restriction to a hyperplane. -/
lemma isCoherent_restrictL {n : ℕ} {M : GradedModule k (n + 1)} (hM : C.IsCoherent M)
    (c : Fin (n + 2) → k) (j : Fin (n + 2)) (hj : IsUnit (c j)) :
    C.IsCoherent (M.restrictL c j) :=
  C.isCoherent_dropVar (C.isCoherent_quotL hM c) c j hj
    (fun d e h => quotL_mulL_eq_zero M c d e h)

/-- The image of `Hⁱ(M(-1)) → Hⁱ(M)` is the image of multiplication by the linear form on the
graded cohomology module. -/
lemma range_map_mulLHom {n : ℕ} (M : GradedModule k n) (c : Fin (n + 1) → k) (i : ℕ) (d : ℤ) :
    LinearMap.range ((C.map (M.mulLHom c) i).app d).hom
      = LinearMap.range ((C.Hgr M i).mulL c (d + -1) d (by ring)).hom := by
  rw [← C.map_mulLHom M c i d, ModuleCat.hom_comp, LinearMap.range_comp]
  have htop : LinearMap.range ((C.twistIso M (-1) i d).inv).hom = ⊤ :=
    LinearMap.range_eq_top.mpr (C.twistIso M (-1) i d).symm.toLinearEquiv.surjective
  rw [htop, Submodule.map_top]

/-- `h⁰(ℙⁿ, 𝒪(d)) = C(n+d, n)` for `d ≥ 0`: the global sections of `𝒪(d)` are the forms of
degree `d`, of which there are `C(n+d, n)`. In particular the value is independent of the base
field, which is what makes the bound of Theorem 2.3.8 uniform. -/
lemma finrank_HgrZero_structureModule {n : ℕ} (d : ℤ) (hd : 0 ≤ d) :
    Module.finrank k ((C.Hgr (structureModule k n) 0).obj d) = ((n : ℤ) + d).toNat.choose n := by
  rw [(C.hgrZeroStructureIso d hd).toLinearEquiv.finrank_eq]
  exact finrank_polySubmodule n hd

/-- The alternating telescoping identity underlying additivity of the Euler characteristic. -/
lemma alternating_telescope (T : ℕ → ℤ) : ∀ N : ℕ,
    ∑ i ∈ Finset.range (N + 1),
        (-1 : ℤ) ^ i * ((if i = 0 then 0 else T (i - 1)) + T i) = (-1 : ℤ) ^ N * T N := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : (if N + 1 = 0 then (0 : ℤ) else T (N + 1 - 1)) = T N := by simp
      rw [h1, pow_succ]
      ring

/-- The Euler characteristic is additive in short exact sequences: the alternating sum of the
dimensions along the long exact sequence vanishes.

The proof is the standard one: rank–nullity at each map of the long exact sequence expresses
`hⁱ(M) - hⁱ(N) + hⁱ(P)` as `tᵢ₋₁ + tᵢ`, where `tᵢ` is the rank of the `i`-th connecting map;
the alternating sum telescopes to `(-1)ⁿ tₙ`, which vanishes because `Hⁿ⁺¹(M) = 0`. -/
lemma chi_add {n : ℕ} {M N P : GradedModule k n} {f : M ⟶ N} {g : N ⟶ P}
    (hfg : ShortExact f g) (hM : C.IsCoherent M) (hN : C.IsCoherent N) (hP : C.IsCoherent P)
    (d : ℤ) : C.chi N d = C.chi M d + C.chi P d := by
  classical
  have fdM : ∀ i, FiniteDimensional k ((C.Hgr M i).obj d) := fun i => C.finiteDimensional hM i d
  have fdN : ∀ i, FiniteDimensional k ((C.Hgr N i).obj d) := fun i => C.finiteDimensional hN i d
  have fdP : ∀ i, FiniteDimensional k ((C.Hgr P i).obj d) := fun i => C.finiteDimensional hP i d
  set r : ℕ → ℤ := fun i =>
    (Module.finrank k (LinearMap.range ((C.map f i).app d).hom) : ℤ) with hr
  set s : ℕ → ℤ := fun i =>
    (Module.finrank k (LinearMap.range ((C.map g i).app d).hom) : ℤ) with hs
  set T : ℕ → ℤ := fun i =>
    (Module.finrank k (LinearMap.range (C.δ hfg i d).hom) : ℤ) with hT
  -- rank–nullity at the three families of maps
  have hMzero : (C.h M 0 d : ℤ) = r 0 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker ((C.map f 0).app d).hom
    have hker : LinearMap.ker ((C.map f 0).app d).hom = ⊥ :=
      LinearMap.ker_eq_bot.mpr (C.injective_map_zero hfg d)
    rw [hker, finrank_bot] at hrn
    have : Module.finrank k ((C.Hgr M 0).obj d) = C.h M 0 d := rfl
    simp only [hr]
    omega
  have hMsucc : ∀ i : ℕ, (C.h M (i + 1) d : ℤ) = r (i + 1) + T i := by
    intro i
    have hrn := LinearMap.finrank_range_add_finrank_ker ((C.map f (i + 1)).app d).hom
    have hker : LinearMap.ker ((C.map f (i + 1)).app d).hom
        = LinearMap.range (C.δ hfg i d).hom := (C.exact_δ_map hfg i d).linearMap_ker_eq
    rw [hker] at hrn
    have : Module.finrank k ((C.Hgr M (i + 1)).obj d) = C.h M (i + 1) d := rfl
    simp only [hr, hT]
    omega
  have hNi : ∀ i : ℕ, (C.h N i d : ℤ) = s i + r i := by
    intro i
    have hrn := LinearMap.finrank_range_add_finrank_ker ((C.map g i).app d).hom
    have hker : LinearMap.ker ((C.map g i).app d).hom
        = LinearMap.range ((C.map f i).app d).hom := (C.exact_map_map hfg i d).linearMap_ker_eq
    rw [hker] at hrn
    have : Module.finrank k ((C.Hgr N i).obj d) = C.h N i d := rfl
    simp only [hr, hs]
    omega
  have hPi : ∀ i : ℕ, (C.h P i d : ℤ) = T i + s i := by
    intro i
    have hrn := LinearMap.finrank_range_add_finrank_ker (C.δ hfg i d).hom
    have hker : LinearMap.ker (C.δ hfg i d).hom
        = LinearMap.range ((C.map g i).app d).hom := (C.exact_map_δ hfg i d).linearMap_ker_eq
    rw [hker] at hrn
    have : Module.finrank k ((C.Hgr P i).obj d) = C.h P i d := rfl
    simp only [hs, hT]
    omega
  -- the top connecting map lands in a zero group
  have hTn : T n = 0 := by
    have hsub : Subsingleton ((C.Hgr M (n + 1)).obj d) :=
      C.subsingleton_of_lt M (n + 1) d (by omega)
    have hbot : LinearMap.range (C.δ hfg n d).hom = ⊥ :=
      (Submodule.eq_bot_iff _).mpr fun x _ => Subsingleton.elim _ _
    have hz : (Module.finrank k (LinearMap.range (C.δ hfg n d).hom) : ℤ) = 0 := by
      rw [hbot, finrank_bot, Nat.cast_zero]
    exact hz
  -- assemble
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ i * (C.h N i d : ℤ)
        = (-1 : ℤ) ^ i * (C.h M i d : ℤ) + (-1 : ℤ) ^ i * (C.h P i d : ℤ)
          - (-1 : ℤ) ^ i * ((if i = 0 then 0 else T (i - 1)) + T i) := by
    intro i _
    rcases i with _ | i
    · rw [hMzero, hNi 0, hPi 0]
      simp
      ring
    · rw [hMsucc i, hNi (i + 1), hPi (i + 1)]
      have hif : (if i + 1 = 0 then (0 : ℤ) else T (i + 1 - 1)) = T i := by simp
      rw [hif]
      ring
  have hsum : C.chi N d = C.chi M d + C.chi P d
      - ∑ i ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ i * ((if i = 0 then 0 else T (i - 1)) + T i) := by
    rw [chi, chi, chi, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl hterm
  rw [hsum, alternating_telescope T n, hTn, mul_zero, sub_zero]

/-- The Euler characteristic of a twist is the Euler characteristic at the shifted degree. -/
lemma chi_twist {n : ℕ} (M : GradedModule k n) (a d : ℤ) :
    C.chi (M.twist a) d = C.chi M (d + a) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg _ (congrArg _ ((C.twistIso M a i d).toLinearEquiv.finrank_eq))

/-- Additivity applied to `0 → F(-1) → F → F|_H → 0`: the Euler characteristic of the
restriction to a hyperplane is the first difference of that of `F`. -/
lemma chi_quotL {n : ℕ} {M : GradedModule k n} (hM : C.IsCoherent M) (c : Fin (n + 1) → k)
    (hL : ∀ d, Function.Injective ((M.mulLHom c).app d).hom) (d : ℤ) :
    C.chi (M.quotL c) d = C.chi M d - C.chi M (d + -1) := by
  have hSE : ShortExact (M.mulLHom c) (toCoker (M.mulLHom c)) := shortExact_toCoker _ hL
  have hadd := C.chi_add hSE (C.isCoherent_twist hM (-1)) hM (C.isCoherent_quotL hM c) d
  rw [C.chi_twist M (-1) d] at hadd
  have hq : C.chi (M.quotL c) d = C.chi (coker (M.mulLHom c)) d := rfl
  rw [hq]
  omega

/-- The cohomological dimensions of `F|_H` on `H ≅ ℙⁿ` agree with those of its pushforward. -/
lemma finrank_Hgr_restrictL {n : ℕ} (M : GradedModule k (n + 1)) (c : Fin (n + 2) → k)
    (j : Fin (n + 2)) (hj : IsUnit (c j)) (hcoh : C.IsCoherent (M.restrictL c j))
    (i : ℕ) (d : ℤ) :
    Module.finrank k ((C.Hgr (M.restrictL c j) i).obj d)
      = Module.finrank k ((C.Hgr (M.quotL c) i).obj d) := by
  have hkill : ∀ (a b : ℤ) (h : a + 1 = b), (M.quotL c).mulL c a b h = 0 :=
    fun a b h => quotL_mulL_eq_zero M c a b h
  exact (isoApp (C.dropVarIso (M.quotL c) c j hj hkill hcoh i) d).toLinearEquiv.finrank_eq

/-- The Euler characteristic of `F|_H` computed on `H ≅ ℙⁿ` agrees with that of its
pushforward computed on `ℙⁿ⁺¹`: the extra term in degree `n+1` vanishes because a sheaf
supported on a hyperplane has no cohomology above `n`. -/
lemma chi_restrictL {n : ℕ} (M : GradedModule k (n + 1)) (c : Fin (n + 2) → k)
    (j : Fin (n + 2)) (hj : IsUnit (c j)) (hcoh : C.IsCoherent (M.restrictL c j)) (d : ℤ) :
    C.chi (M.restrictL c j) d = C.chi (M.quotL c) d := by
  have htop : C.h (M.quotL c) (n + 1) d = 0 := by
    refine C.h_eq_zero_of_subsingleton ?_
    rw [← C.subsingleton_Hgr_restrictL_iff M c j hj hcoh]
    exact C.subsingleton_of_lt (M.restrictL c j) (n + 1) d (by omega)
  have h1 : C.chi (M.quotL c) d
      = (∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (C.h (M.quotL c) i d : ℤ))
        + (-1 : ℤ) ^ (n + 1) * (C.h (M.quotL c) (n + 1) d : ℤ) := Finset.sum_range_succ _ _
  rw [h1, htop]
  simp only [Nat.cast_zero, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hfr : (C.h (M.restrictL c j) i d : ℤ) = (C.h (M.quotL c) i d : ℤ) :=
    congrArg _ (C.finrank_Hgr_restrictL M c j hj hcoh i d)
  rw [hfr]

end Cohomology

namespace Cohomology

/-- If `A → B → D` is exact and `A` and `D` vanish, so does `B`. -/
lemma subsingleton_of_exact {k : Type u} [Field k] {A B D : ModuleCat.{u} k} (u : A ⟶ B)
    (v : B ⟶ D)
    (huv : Function.Exact u.hom v.hom) (hA : Subsingleton A) (hD : Subsingleton D) :
    Subsingleton B := by
  have key : ∀ z : B, z = 0 := by
    intro z
    obtain ⟨a, ha⟩ := (huv z).mp (Subsingleton.elim _ _)
    rw [← ha, Subsingleton.elim a 0, map_zero]
  exact ⟨fun x y => by rw [key x, key y]⟩

variable {k : Type u} [Field k] (C : Cohomology k)
variable {n : ℕ} {M N P : GradedModule k n} {f : M ⟶ N} {g : N ⟶ P}

/-- Vanishing propagates along the long exact sequence: if `Hⁱ(N)` and `Hⁱ⁺¹(M)` vanish, so
does `Hⁱ(P)`. -/
lemma subsingleton_H_X₃ (hfg : ShortExact f g) (i : ℕ) (d : ℤ)
    (h₁ : Subsingleton ((C.Hgr N i).obj d)) (h₂ : Subsingleton ((C.Hgr M (i + 1)).obj d)) :
    Subsingleton ((C.Hgr P i).obj d) :=
  subsingleton_of_exact _ _ (C.exact_map_δ hfg i d) h₁ h₂

/-- Vanishing propagates along the long exact sequence: if `Hⁱ(M)` and `Hⁱ(P)` vanish, so
does `Hⁱ(N)`. -/
lemma subsingleton_H_X₂ (hfg : ShortExact f g) (i : ℕ) (d : ℤ)
    (h₁ : Subsingleton ((C.Hgr M i).obj d)) (h₂ : Subsingleton ((C.Hgr P i).obj d)) :
    Subsingleton ((C.Hgr N i).obj d) :=
  subsingleton_of_exact _ _ (C.exact_map_map hfg i d) h₁ h₂

/-- Vanishing propagates along the long exact sequence: if `Hⁱ(P)` and `Hⁱ⁺¹(N)` vanish, so
does `Hⁱ⁺¹(M)`. -/
lemma subsingleton_H_X₁ (hfg : ShortExact f g) (i : ℕ) (d : ℤ)
    (h₁ : Subsingleton ((C.Hgr P i).obj d)) (h₂ : Subsingleton ((C.Hgr N (i + 1)).obj d)) :
    Subsingleton ((C.Hgr M (i + 1)).obj d) :=
  subsingleton_of_exact _ _ (C.exact_δ_map hfg i d) h₁ h₂

/-- If `Hⁱ⁺¹(M)` vanishes then `Hⁱ(N) → Hⁱ(P)` is surjective. -/
lemma surjective_map_of_subsingleton (hfg : ShortExact f g) (i : ℕ) (d : ℤ)
    (h : Subsingleton ((C.Hgr M (i + 1)).obj d)) :
    Function.Surjective ((C.map g i).app d).hom := fun z =>
  (C.exact_map_δ hfg i d z).mp (Subsingleton.elim _ _)

/-- If `Hⁱ(P)` vanishes then `Hⁱ(M) → Hⁱ(N)` is surjective. -/
lemma surjective_map_fst_of_subsingleton (hfg : ShortExact f g) (i : ℕ) (d : ℤ)
    (h : Subsingleton ((C.Hgr P i).obj d)) :
    Function.Surjective ((C.map f i).app d).hom := fun z =>
  (C.exact_map_map hfg i d z).mp (Subsingleton.elim _ _)

/-- If `Hⁱ(N)` vanishes then `Hⁱ(P) → Hⁱ⁺¹(M)` is injective. -/
lemma injective_δ_of_subsingleton (hfg : ShortExact f g) (i : ℕ) (d : ℤ)
    (h : Subsingleton ((C.Hgr N i).obj d)) : Function.Injective (C.δ hfg i d).hom := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, hy⟩ := (C.exact_map_δ hfg i d z).mp hz
  rw [← hy, Subsingleton.elim y 0, map_zero]

/-- The image of the connecting map is the kernel of `Hⁱ⁺¹(M) → Hⁱ⁺¹(N)`. -/
lemma range_δ (hfg : ShortExact f g) (i : ℕ) (d : ℤ) :
    LinearMap.range (C.δ hfg i d).hom = LinearMap.ker ((C.map f (i + 1)).app d).hom :=
  ((C.exact_δ_map hfg i d).linearMap_ker_eq).symm

/-- The connecting map vanishes exactly when `Hⁱ(N) → Hⁱ(P)` is surjective. -/
lemma range_δ_eq_bot_iff (hfg : ShortExact f g) (i : ℕ) (d : ℤ) :
    LinearMap.range (C.δ hfg i d).hom = ⊥ ↔
      Function.Surjective ((C.map g i).app d).hom := by
  constructor
  · intro hδ z
    exact (C.exact_map_δ hfg i d z).mp
      ((Submodule.eq_bot_iff _).mp hδ _ (LinearMap.mem_range_self _ z))
  · intro hsurj
    refine (Submodule.eq_bot_iff _).mpr ?_
    rintro x ⟨z, rfl⟩
    obtain ⟨y, rfl⟩ := hsurj z
    have := (C.exact_map_δ hfg i d) (((C.map g i).app d).hom y)
    exact (this.mpr ⟨y, rfl⟩)

end Cohomology

/-- Flat base change of the graded-module model along a field extension `k ⊆ k'`: it takes
coherent sheaves to coherent sheaves, subsheaves of `𝒪^{⊕r}` to subsheaves of `𝒪^{⊕r}`, and
preserves every cohomological dimension.

This packages the input to the first paragraph of the proof of Proposition 2.3.5: "if `k → k'`
is a field extension, then Flat Base Change implies `Hⁱ(ℙⁿ_k, F) ⊗_k k' = Hⁱ(ℙⁿ_{k'}, F ⊗_k k')`,
and as `k → k'` is faithfully flat the assertions can be checked after base change". -/
structure Cohomology.BaseChange {k k' : Type u} [Field k] [Field k']
    (C : Cohomology k) (C' : Cohomology k') where
  /-- The base-changed sheaf. -/
  obj : ∀ {n : ℕ}, GradedModule k n → GradedModule k' n
  /-- Base change preserves coherence. -/
  isCoherent : ∀ {n : ℕ} (M : GradedModule k n), C.IsCoherent M → C'.IsCoherent (obj M)
  /-- Base change preserves every cohomological dimension. -/
  finrank_eq : ∀ {n : ℕ} (M : GradedModule k n) (i : ℕ) (d : ℤ),
    Module.finrank k' ((C'.Hgr (obj M) i).obj d) = Module.finrank k ((C.Hgr M i).obj d)
  /-- Base change is faithfully flat, so vanishing may be detected after base change. -/
  subsingleton_iff : ∀ {n : ℕ} (M : GradedModule k n) (i : ℕ) (d : ℤ),
    Subsingleton ((C'.Hgr (obj M) i).obj d) ↔ Subsingleton ((C.Hgr M i).obj d)
  /-- Base change preserves and reflects the multiplication spans of the graded cohomology
  modules, i.e. global generation. -/
  mulSpan_iff : ∀ {n : ℕ} (M : GradedModule k n) (i : ℕ) (d e : ℤ),
    ((C'.Hgr (obj M) i).mulSpan d e = ⊤ ↔ (C.Hgr M i).mulSpan d e = ⊤)
  /-- Base change preserves and reflects global generation. -/
  isGloballyGenerated_iff : ∀ {n : ℕ} (M : GradedModule k n) (d : ℤ),
    (C'.IsGloballyGenerated (obj M) d ↔ C.IsGloballyGenerated M d)
  /-- Base change of a subsheaf of `𝒪^{⊕r}` is a subsheaf of `𝒪^{⊕r}`. -/
  mono : ∀ {n r : ℕ} {M : GradedModule k n} (f : M ⟶ (structureModule k n).pow r),
    (∀ d, Function.Injective (f.app d).hom) →
    ∃ f' : obj M ⟶ (structureModule k' n).pow r, ∀ d, Function.Injective (f'.app d).hom

namespace Cohomology.BaseChange

/-- The identity base change of a packaged projective cohomology theory. -/
def refl {k : Type u} [Field k] (C : Cohomology k) : Cohomology.BaseChange C C where
  obj M := M
  isCoherent _ hM := hM
  finrank_eq _ _ _ := rfl
  subsingleton_iff _ _ _ := Iff.rfl
  mulSpan_iff _ _ _ _ := Iff.rfl
  isGloballyGenerated_iff _ _ := Iff.rfl
  mono f hf := ⟨f, hf⟩

/-- Composition of packaged base changes. -/
def comp {k₀ k₁ k₂ : Type u} [Field k₀] [Field k₁] [Field k₂]
    {C₀ : Cohomology k₀} {C₁ : Cohomology k₁} {C₂ : Cohomology k₂}
    (B₀₁ : Cohomology.BaseChange C₀ C₁) (B₁₂ : Cohomology.BaseChange C₁ C₂) :
    Cohomology.BaseChange C₀ C₂ where
  obj M := B₁₂.obj (B₀₁.obj M)
  isCoherent M hM := B₁₂.isCoherent _ (B₀₁.isCoherent M hM)
  finrank_eq M i d := (B₁₂.finrank_eq (B₀₁.obj M) i d).trans (B₀₁.finrank_eq M i d)
  subsingleton_iff M i d :=
    (B₁₂.subsingleton_iff (B₀₁.obj M) i d).trans (B₀₁.subsingleton_iff M i d)
  mulSpan_iff M i d e :=
    (B₁₂.mulSpan_iff (B₀₁.obj M) i d e).trans (B₀₁.mulSpan_iff M i d e)
  isGloballyGenerated_iff M d :=
    (B₁₂.isGloballyGenerated_iff (B₀₁.obj M) d).trans
      (B₀₁.isGloballyGenerated_iff M d)
  mono f hf := by
    obtain ⟨f₁, hf₁⟩ := B₀₁.mono f hf
    exact B₁₂.mono f₁ hf₁

/-- Equality of packaged cohomology theories induces a base change. -/
def of_eq {k : Type u} [Field k] {C C' : Cohomology k} (h : C = C') :
    Cohomology.BaseChange C C' := by
  subst h
  exact refl C

/-- A packaged base change preserves every individual cohomology dimension. -/
lemma h_eq {k k' : Type u} [Field k] [Field k'] {C : Cohomology k} {C' : Cohomology k'}
    (B : Cohomology.BaseChange C C') {n : ℕ} (M : GradedModule k n) (i : ℕ) (d : ℤ) :
    C'.h (B.obj M) i d = C.h M i d :=
  B.finrank_eq M i d

/-- A packaged base change preserves the Euler characteristic. -/
lemma chi_eq {k k' : Type u} [Field k] [Field k'] {C : Cohomology k} {C' : Cohomology k'}
    (B : Cohomology.BaseChange C C') {n : ℕ} (M : GradedModule k n) (d : ℤ) :
    C'.chi (B.obj M) d = C.chi M d := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [B.h_eq M i d]

/-- A packaged base change preserves and reflects the Hilbert polynomial. -/
lemma hasHilbertPolynomial_iff {k k' : Type u} [Field k] [Field k']
    {C : Cohomology k} {C' : Cohomology k'} (B : Cohomology.BaseChange C C') {n : ℕ}
    (M : GradedModule k n) (P : Polynomial ℚ) :
    C'.HasHilbertPolynomial (B.obj M) P ↔ C.HasHilbertPolynomial M P := by
  constructor
  · intro h d
    rw [← B.chi_eq M d]
    exact h d
  · intro h d
    rw [B.chi_eq M d]
    exact h d

end Cohomology.BaseChange

/-- The rational-function field is an explicit infinite field extension of any field. -/
lemma Cohomology.infinite_ratFunc (k : Type u) [Field k] : Infinite (RatFunc k) :=
  Infinite.of_injective (algebraMap (Polynomial k) (RatFunc k))
    (RatFunc.algebraMap_injective k)

/-- Every field has an infinite extension in the same universe. This discharges the purely
field-theoretic part of the infinite-base-field reduction; constructing the corresponding
cohomology theory and its base-change comparison is separate. -/
theorem Cohomology.exists_infinite_field_extension (k : Type u) [Field k] :
    ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k'), Infinite k' := by
  let _ : Infinite (RatFunc k) := Cohomology.infinite_ratFunc k
  exact ⟨RatFunc k, inferInstance, inferInstance, inferInstance⟩

/-- It suffices to construct the cohomology theory and comparison over the explicit infinite
extension `k(t)`. This isolates the geometric base-change content from existence of an infinite
field extension. -/
theorem Cohomology.exists_infinite_baseChange_of_ratFunc
    {k : Type u} [Field k] (C : Cohomology k) (C' : Cohomology (RatFunc k))
    (B : Nonempty (Cohomology.BaseChange C C')) :
    ∃ (k' : Type u) (_ : Field k') (C'' : Cohomology k'), Infinite k' ∧
      Nonempty (Cohomology.BaseChange C C'') := by
  let _ : Infinite (RatFunc k) := Cohomology.infinite_ratFunc k
  exact ⟨RatFunc k, inferInstance, C', inferInstance, B⟩

/-- If the ground field is already infinite, the identity base change supplies the
infinite-field reduction used in the regularity arguments. -/
theorem Cohomology.exists_infinite_baseChange_of_infinite
    {k : Type u} [Field k] [Infinite k] (C : Cohomology k) :
    ∃ (k' : Type u) (_ : Field k') (C' : Cohomology k'), Infinite k' ∧
      Nonempty (Cohomology.BaseChange C C') :=
  ⟨k, inferInstance, C, inferInstance, ⟨Cohomology.BaseChange.refl C⟩⟩

/-- The general infinite-base-change assertion reduces to its finite-ground-field case: the
infinite-ground-field branch is the identity comparison. -/
theorem Cohomology.has_infinite_baseChange_iff_finite_case
    {k : Type u} [Field k] (C : Cohomology k) :
    (∃ (k' : Type u) (_ : Field k') (C' : Cohomology k'), Infinite k' ∧
        Nonempty (Cohomology.BaseChange C C')) ↔
      (Finite k → ∃ (k' : Type u) (_ : Field k') (C' : Cohomology k'), Infinite k' ∧
        Nonempty (Cohomology.BaseChange C C')) := by
  constructor
  · exact fun h _ => h
  · intro h
    rcases finite_or_infinite k with hk | hk
    · exact h hk
    · let _ : Infinite k := hk
      exact Cohomology.exists_infinite_baseChange_of_infinite C

/- The obligation `Cohomology.nonempty` is **discharged** in
`StacksAndModuli/API/ProjectiveGradedCohomologyExists.lean`: the graded Čech complex of the standard
affine cover supplies every field, with the five substantive Serre-theoretic inputs packaged
as `CechSerreData` and proved in `API/ProjectiveGradedSerre.lean` (finiteness and vanishing),
`API/ProjectiveGradedTorsion.lean` (the torsion-free model), `API/ProjectiveGradedTotal.lean`
(prime avoidance) and `API/ProjectiveGradedDropVarLoc.lean` (the hyperplane comparison). -/

/-- **Reduction to an infinite base field.** The ground field `k` embeds into an infinite
field `k'` in the same universe, and `C` admits a flat base-change comparison to a cohomology
theory over `k'`. This is the first step of the proofs of Proposition 2.3.5 and Theorem 2.3.8:
"if `k → k'` is a field extension, then Flat Base Change implies
`Hⁱ(ℙⁿ_k, F) ⊗_k k' = Hⁱ(ℙⁿ_{k'}, F ⊗_k k')`, and as `k → k'` is faithfully flat the
assertions can be checked after base change".

This holds for the canonical Čech theory — `Cohomology.hasInfiniteBaseChange_cech`, proved in
`API/ProjectiveGradedBaseChange.lean` — but it is carried as a hypothesis rather than being an
axiom of `Cohomology`, because it is *not* derivable for a general term of `Cohomology k`: the
axioms do not pin down `Hgr M i` for non-coherent `M`, whereas `BaseChange.finrank_eq` compares
dimensions for every `M`. See `StacksAndModuli/Section2.3-Regularity/COMMENTARY.md`. -/
def Cohomology.HasInfiniteBaseChange {k : Type u} [Field k] (C : Cohomology k) : Prop :=
  ∃ (k' : Type u) (_ : Field k') (C' : Cohomology k'), Infinite k' ∧
    Nonempty (Cohomology.BaseChange C C')

/-- Over an infinite ground field the identity comparison suffices. -/
theorem Cohomology.hasInfiniteBaseChange_of_infinite {k : Type u} [Field k] [Infinite k]
    (C : Cohomology k) : C.HasInfiniteBaseChange :=
  Cohomology.exists_infinite_baseChange_of_infinite C

/-- The infinite-base-change hypothesis transports along a packaged base change. -/
theorem Cohomology.HasInfiniteBaseChange.of_baseChange {k k' : Type u} [Field k] [Field k']
    {C : Cohomology k} {C' : Cohomology k'} (B : Cohomology.BaseChange C C')
    (h : C'.HasInfiniteBaseChange) : C.HasInfiniteBaseChange := by
  obtain ⟨k'', _, C'', hinf, ⟨B'⟩⟩ := h
  exact ⟨k'', inferInstance, C'', hinf, ⟨B.comp B'⟩⟩

end AlgebraicGeometry.ProjectiveSpace
