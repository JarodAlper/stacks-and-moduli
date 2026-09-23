module

public import StacksAndModuli.API.ProjectiveGradedCohomology
public import StacksAndModuli.API.FiniteProjectiveFiberRank
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Families of quasi-coherent sheaves on projective space, in the graded-module model

Supporting API with no Stacks Project counterpart, developed for §2.3 (Castelnuovo–Mumford
regularity) of *Stacks and Moduli* — specifically **Proposition 2.3.18**
(`prop:regularity-in-families`).

`StacksAndModuli/API/ProjectiveGradedModule.lean` already works over an arbitrary commutative ring, so
a family of quasi-coherent sheaves on `ℙⁿ_S` over an affine base `S = Spec R` is a
`GradedModule R n`, and its fibre at a point is the base change to the residue field. This file
adds the base change of graded modules and packages the *relative* cohomology
`⨁_d Rⁱπ_* M~(d)` together with Cohomology and Base Change (§A.6, `thm:cbc`), which is what the
proof of Proposition 2.3.18 quotes.

As in the absolute case, constructing the relative cohomology is out of reach — Mathlib has no
higher direct images — so it is packaged as a structure `RelativeCohomology R`, and
Proposition 2.3.18 is proved relative to a term of it. The mathematical content of that proof
is the passage from *fibrewise regularity* to *fibrewise vanishing*, which is
`Cohomology.subsingleton_Hgr_of_le_of_field` (Proposition 2.3.5(3), proved), followed by an
application of Cohomology and Base Change.

Main declarations:
- `AlgebraicGeometry.ProjectiveSpace.GradedModule.baseChange`: base change of a graded module.
- `AlgebraicGeometry.ProjectiveSpace.RelativeCohomology`: the packaged relative cohomology.
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

namespace AlgebraicGeometry.ProjectiveSpace

open CategoryTheory GradedModule TensorProduct

/-- Base change of a graded module along a ring homomorphism `R → A`: the graded `A`-module
whose degree-`d` piece is `A ⊗_R M_d`. It models the pullback of a family of quasi-coherent
sheaves on `ℙⁿ_R` along `Spec A → Spec R`; the fibre of the family at a point of `Spec R` is
the base change to the residue field. -/
noncomputable def GradedModule.baseChange {R : Type u} [CommRing R] {n : ℕ}
    (M : GradedModule R n) (A : Type u) [CommRing A] [Algebra R A] : GradedModule A n where
  obj d := ModuleCat.of A (A ⊗[R] (M.obj d))
  mulX i d := ModuleCat.ofHom (LinearMap.baseChange A (M.mulX i d).hom)
  mulX_comm i j d := by
    have h := congrArg (fun f : M.obj d ⟶ M.obj (d + 1 + 1) =>
      ModuleCat.ofHom (LinearMap.baseChange A f.hom)) (M.mulX_comm i j d)
    simpa [ModuleCat.ofHom_comp, LinearMap.baseChange_comp] using h

/-- Base change of a morphism of graded modules. -/
noncomputable def GradedModule.baseChangeMap {R : Type u} [CommRing R] {n : ℕ}
    {M N : GradedModule R n} (f : M ⟶ N) (A : Type u) [CommRing A] [Algebra R A] :
    M.baseChange A ⟶ N.baseChange A where
  app d := ModuleCat.ofHom (LinearMap.baseChange A (f.app d).hom)
  comm i d := by
    have h := congrArg (fun u : M.obj d ⟶ N.obj (d + 1) =>
      ModuleCat.ofHom (LinearMap.baseChange A u.hom)) (f.comm i d)
    simpa [GradedModule.baseChange, ModuleCat.ofHom_comp, ModuleCat.hom_comp,
      LinearMap.baseChange_comp] using h

@[simp] lemma GradedModule.baseChange_obj {R : Type u} [CommRing R] {n : ℕ}
    (M : GradedModule R n) (A : Type u) [CommRing A] [Algebra R A] (d : ℤ) :
    (M.baseChange A).obj d = ModuleCat.of A (A ⊗[R] (M.obj d)) := rfl

/-- The cohomology of *families* of quasi-coherent sheaves on `ℙⁿ_R` over an affine base
`Spec R`, in the graded-module model, packaged with the fibrewise comparison and Cohomology
and Base Change.

`Hgr M i` is the graded `R`-module `⨁_d Γ(Spec R, Rⁱπ_* M~(d))`. The fibre of the family `M`
at a point of `Spec R` with residue field `κ` is `M.baseChange κ`, a graded module over `κ`
whose cohomology is computed by the absolute theory `fibre κ`.

Constructing a term of this structure is a recorded obligation, `RelativeCohomology.nonempty`;
see `StacksAndModuli/Section2.3-Regularity/COMMENTARY.md`. -/
structure RelativeCohomology (R : Type u) [CommRing R] where
  /-- `Hgr M i` is the graded `R`-module `⨁_d Γ(Spec R, Rⁱπ_* M~(d))`. -/
  Hgr : ∀ {n : ℕ}, GradedModule R n → ℕ → GradedModule R n
  /-- Coherence of a family. -/
  IsCoherent : ∀ {n : ℕ}, GradedModule R n → Prop
  /-- Flatness of a family over the base. -/
  IsFlat : ∀ {n : ℕ}, GradedModule R n → Prop
  /-- The absolute cohomology theory of the fibre over a residue field of the base. -/
  fibre : ∀ (κ : Type u) [Field κ] [Algebra R κ], Cohomology κ
  /-- Each fibre theory satisfies the infinite-base-field reduction
  (`Cohomology.HasInfiniteBaseChange`); the canonical Čech theory does, by
  `Cohomology.hasInfiniteBaseChange_cech`. -/
  fibre_hasInfiniteBaseChange : ∀ (κ : Type u) [Field κ] [Algebra R κ],
    (fibre κ).HasInfiniteBaseChange
  /-- Fibres of a coherent family are coherent. -/
  isCoherent_fibre : ∀ {n : ℕ} (M : GradedModule R n), IsCoherent M →
    ∀ (κ : Type u) [Field κ] [Algebra R κ], (fibre κ).IsCoherent (M.baseChange κ)
  /-- The structure sheaf is coherent. -/
  isCoherent_structureModule : ∀ {n : ℕ}, IsCoherent (structureModule R n)
  /-- Twists of coherent families are coherent. -/
  isCoherent_twist : ∀ {n : ℕ} {M : GradedModule R n}, IsCoherent M → ∀ a : ℤ,
    IsCoherent (M.twist a)
  /-- Finite direct sums of coherent families are coherent. -/
  isCoherent_pow : ∀ {n : ℕ} {M : GradedModule R n}, IsCoherent M → ∀ r : ℕ,
    IsCoherent (M.pow r)
  /-- Cokernels of maps of coherent families are coherent. -/
  isCoherent_coker : ∀ {n : ℕ} {M N : GradedModule R n} (f : M ⟶ N),
    IsCoherent M → IsCoherent N → IsCoherent (coker f)
  /-- Subfamilies of coherent families are coherent (the base is noetherian). -/
  isCoherent_of_injective : ∀ {n : ℕ} {M N : GradedModule R n} (f : M ⟶ N),
    (∀ d, Function.Injective (f.app d).hom) → IsCoherent N → IsCoherent M
  /-- The structure sheaf is flat over the base. -/
  isFlat_structureModule : ∀ {n : ℕ}, IsFlat (structureModule R n)
  /-- Twists of flat families are flat. -/
  isFlat_twist : ∀ {n : ℕ} {M : GradedModule R n}, IsFlat M → ∀ a : ℤ,
    IsFlat (M.twist a)
  /-- Finite direct sums of flat families are flat. -/
  isFlat_pow : ∀ {n : ℕ} {M : GradedModule R n}, IsFlat M → ∀ r : ℕ,
    IsFlat (M.pow r)
  /-- The kernel of a surjection of flat families with flat quotient is flat.  This is the
  form in which §2.4 needs flatness: for `0 → K → F → Q → 0` with `F` and `Q` flat over the
  base, `K` is flat. -/
  isFlat_of_shortExact : ∀ {n : ℕ} {M N P : GradedModule R n} {f : M ⟶ N} {g : N ⟶ P},
    ShortExact f g → IsFlat N → IsFlat P → IsFlat M
  /-- Relative Serre vanishing, uniformly on field fibres of an affine noetherian base. -/
  uniform_serre_vanishing : ∀ {n : ℕ} (M : GradedModule R n), IsCoherent M → IsFlat M →
    ∃ d₀ : ℤ, ∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      ∀ d : ℤ, d₀ ≤ d → Subsingleton (((fibre κ).Hgr (M.baseChange κ) i).obj d)
  /-- The formation of `π_* M(d)` commutes with base change: for every base change
  `f : T → Spec R` the natural map `f^* π_* M(d) → π_{T,*} M_T(d)` is an isomorphism. -/
  CommutesWithBaseChange : ∀ {n : ℕ}, GradedModule R n → ℤ → Prop
  /-- The comparison isomorphism expressed by `CommutesWithBaseChange`, for a field-valued
  base change. -/
  baseChangeIso : ∀ {n : ℕ} (M : GradedModule R n) (d : ℤ),
    CommutesWithBaseChange M d → ∀ (κ : Type u) [Field κ] [Algebra R κ],
      ModuleCat.of κ (κ ⊗[R] ((Hgr M 0).obj d)) ≅ ((fibre κ).Hgr (M.baseChange κ) 0).obj d
  /-- Global generation of `M(d)` relative to the base: `π^* π_* M(d) → M(d)` is surjective. -/
  IsGloballyGenerated : ∀ {n : ℕ}, GradedModule R n → ℤ → Prop
  /-- Cohomology is a functor. -/
  map : ∀ {n : ℕ} {M N : GradedModule R n}, (M ⟶ N) → ∀ i : ℕ, Hgr M i ⟶ Hgr N i
  /-- The connecting homomorphism of the long exact sequence of higher direct images. -/
  δ : ∀ {n : ℕ} {M N P : GradedModule R n} {f : M ⟶ N} {g : N ⟶ P},
    ShortExact f g → ∀ (i : ℕ) (d : ℤ), (Hgr P i).obj d ⟶ (Hgr M (i + 1)).obj d
  /-- Exactness of the long exact sequence at `Rⁱπ_*(P)`. -/
  exact_map_δ : ∀ {n : ℕ} {M N P : GradedModule R n} {f : M ⟶ N} {g : N ⟶ P}
    (hfg : ShortExact f g) (i : ℕ) (d : ℤ),
    Function.Exact ((map g i).app d).hom (δ hfg i d).hom
  /-- Fibres of a short exact sequence of families whose quotient is flat over the base are
  short exact (the `Tor₁` term vanishes). -/
  shortExact_fibre : ∀ {n : ℕ} {M N P : GradedModule R n} {f : M ⟶ N} {g : N ⟶ P},
    ShortExact f g → IsFlat P → ∀ (κ : Type u) [Field κ] [Algebra R κ],
    ShortExact (GradedModule.baseChangeMap f κ) (GradedModule.baseChangeMap g κ)
  /-- API field modeling **Cohomology and Base Change** (Theorem A.6.8), in the form quoted
  in the proof of Proposition 2.3.18: for a coherent family flat over the base whose fibres
  have vanishing higher cohomology at the twist `d`, the higher direct images vanish at `d`,
  and `π_* M(d)` is a vector bundle whose formation commutes with base change. -/
  cbc : ∀ {n : ℕ} (M : GradedModule R n) (d : ℤ), IsCoherent M → IsFlat M →
    (∀ (κ : Type u) [Field κ] [Algebra R κ] (i : ℕ), 1 ≤ i →
      Subsingleton (((fibre κ).Hgr (M.baseChange κ) i).obj d)) →
    (∀ i : ℕ, 1 ≤ i → Subsingleton ((Hgr M i).obj d)) ∧
      Module.Finite R ((Hgr M 0).obj d) ∧ Module.Projective R ((Hgr M 0).obj d) ∧
      CommutesWithBaseChange M d
  /-- Surjectivity may be checked on fibres (Nakayama): if the higher cohomology vanishes on
  every fibre in every twist `≥ d`, and the fibrewise multiplication maps
  `H⁰(M_κ(d)) ⊗ S_{e-d} → H⁰(M_κ(e))` are surjective for every `e ≥ d`, then
  `π^* π_* M(d) → M(d)` is surjective.

  The hypotheses are the *uniform* form of "every fibre `M_s(d)` is globally generated": the
  cokernel of `π^* π_* M(e) → M(e)` is checked to vanish one twist `e` at a time by Nakayama,
  which needs the comparison `κ ⊗ π_* M(e) ≅ H⁰(M_κ(e))` at every such `e`, and a bound on the
  twist that does not depend on the fibre. Both are what
  `isGloballyGenerated_of_fibres_regular` — the only consumer, and the form Proposition
  2.3.18(3) is used in — actually has available, from `m`-regularity of the fibres. -/
  isGloballyGenerated_of_fibres : ∀ {n : ℕ} (M : GradedModule R n) (d : ℤ), IsCoherent M →
    IsFlat M →
    (∀ (κ : Type u) [Field κ] [Algebra R κ] (e : ℤ), d ≤ e → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (((fibre κ).Hgr (M.baseChange κ) i).obj e)) →
    (∀ (κ : Type u) [Field κ] [Algebra R κ] (e : ℤ), d ≤ e →
      ((fibre κ).Hgr (M.baseChange κ) 0).mulSpan d e = ⊤) →
    IsGloballyGenerated M d

namespace RelativeCohomology

variable {R : Type u} [CommRing R] (Crel : RelativeCohomology R)

/-- If `Rⁱ⁺¹π_*(M)` vanishes at the twist `d` then `Rⁱπ_*(N) → Rⁱπ_*(P)` is surjective there. -/
lemma surjective_map_of_subsingleton {n : ℕ} {M N P : GradedModule R n} {f : M ⟶ N} {g : N ⟶ P}
    (hfg : ShortExact f g) (i : ℕ) (d : ℤ) (h : Subsingleton ((Crel.Hgr M (i + 1)).obj d)) :
    Function.Surjective ((Crel.map g i).app d).hom := fun z =>
  (Crel.exact_map_δ hfg i d z).mp (Subsingleton.elim _ _)

/-- If `π_* M(d)` is finite projective and commutes with base change, then the dimension of
`H⁰(M_κ(d))` is independent of the field-valued point of the local base. -/
lemma finrank_fibre_zero_eq_of_finite_projective_of_isLocalRing [IsLocalRing R]
    {n : ℕ} (M : GradedModule R n) (d : ℤ)
    (hfin : Module.Finite R ((Crel.Hgr M 0).obj d))
    (hproj : Module.Projective R ((Crel.Hgr M 0).obj d))
    (hbc : Crel.CommutesWithBaseChange M d)
    (κ : Type u) [Field κ] [Algebra R κ] :
    Module.finrank κ (((Crel.fibre κ).Hgr (M.baseChange κ) 0).obj d) =
      Module.finrank R ((Crel.Hgr M 0).obj d) := by
  letI : Module.Finite R ((Crel.Hgr M 0).obj d) := hfin
  letI : Module.Projective R ((Crel.Hgr M 0).obj d) := hproj
  rw [← (Crel.baseChangeIso M d hbc κ).toLinearEquiv.finrank_eq]
  exact Module.finrank_tensorProduct_eq_of_finite_projective_of_isLocalRing

/-- Under finite-projective cohomology and base change, any two field fibres have equal
dimensions of global sections in the chosen twist. -/
lemma finrank_fibre_zero_eq_fibre_zero_of_finite_projective_of_isLocalRing [IsLocalRing R]
    {n : ℕ} (M : GradedModule R n) (d : ℤ)
    (hfin : Module.Finite R ((Crel.Hgr M 0).obj d))
    (hproj : Module.Projective R ((Crel.Hgr M 0).obj d))
    (hbc : Crel.CommutesWithBaseChange M d)
    (κ κ' : Type u) [Field κ] [Algebra R κ] [Field κ'] [Algebra R κ'] :
    Module.finrank κ (((Crel.fibre κ).Hgr (M.baseChange κ) 0).obj d) =
      Module.finrank κ' (((Crel.fibre κ').Hgr (M.baseChange κ') 0).obj d) := by
  rw [Crel.finrank_fibre_zero_eq_of_finite_projective_of_isLocalRing M d hfin hproj hbc κ,
    Crel.finrank_fibre_zero_eq_of_finite_projective_of_isLocalRing M d hfin hproj hbc κ']

/-- For a coherent flat family over a local base, the dimensions of global sections on any
two field fibres agree in every sufficiently large twist. -/
theorem eventually_finrank_fibre_zero_eq_fibre_zero [IsLocalRing R]
    {n : ℕ} (M : GradedModule R n) (hM : Crel.IsCoherent M) (hflat : Crel.IsFlat M)
    (κ κ' : Type u) [Field κ] [Algebra R κ] [Field κ'] [Algebra R κ'] :
    ∀ᶠ d : ℕ in Filter.atTop,
      Module.finrank κ (((Crel.fibre κ).Hgr (M.baseChange κ) 0).obj (d : ℤ)) =
        Module.finrank κ' (((Crel.fibre κ').Hgr (M.baseChange κ') 0).obj (d : ℤ)) := by
  obtain ⟨d₀, hd₀⟩ := Crel.uniform_serre_vanishing M hM hflat
  filter_upwards [Filter.eventually_ge_atTop d₀.toNat] with d hd
  have hd' : d₀ ≤ (d : ℤ) := by omega
  obtain ⟨-, hfin, hproj, hbc⟩ := Crel.cbc M (d : ℤ) hM hflat
    (fun L _ _ i hi ↦ hd₀ L i hi (d : ℤ) hd')
  exact Crel.finrank_fibre_zero_eq_fibre_zero_of_finite_projective_of_isLocalRing
    M (d : ℤ) hfin hproj hbc κ κ'

/-- The eventual `H⁰` definition of the Hilbert polynomial of a field fibre in the
graded-module model. -/
def HasHilbertPolynomialOnFibre {n : ℕ} (M : GradedModule R n)
    (κ : Type u) [Field κ] [Algebra R κ] (P : Polynomial ℚ) : Prop :=
  ∀ᶠ d : ℕ in Filter.atTop,
    (Module.finrank κ (((Crel.fibre κ).Hgr (M.baseChange κ) 0).obj (d : ℤ)) : ℚ) =
      P.eval (d : ℚ)

/-- A coherent flat family over a local base has the same Hilbert polynomial on every pair
of field fibres. -/
theorem hasHilbertPolynomialOnFibre_iff [IsLocalRing R]
    {n : ℕ} (M : GradedModule R n) (hM : Crel.IsCoherent M) (hflat : Crel.IsFlat M)
    (κ κ' : Type u) [Field κ] [Algebra R κ] [Field κ'] [Algebra R κ']
    (P : Polynomial ℚ) :
    Crel.HasHilbertPolynomialOnFibre M κ P ↔
      Crel.HasHilbertPolynomialOnFibre M κ' P := by
  have heq := Crel.eventually_finrank_fibre_zero_eq_fibre_zero M hM hflat κ κ'
  constructor
  · intro h
    filter_upwards [h, heq] with d hd heqd
    rw [← heqd]
    exact hd
  · intro h
    filter_upwards [h, heq] with d hd heqd
    rw [heqd]
    exact hd

end RelativeCohomology

/- The obligation `RelativeCohomology.nonempty` is **discharged** in
`StacksAndModuli/API/ProjectiveGradedRelativeExists.lean`: `RelativeCohomology.cech R` is the graded
Čech complex of the standard affine cover over a noetherian ring `R`, with Serre finiteness and
vanishing from `API/ProjectiveGradedSerre.lean` (stated over any noetherian ring), degreewise
flatness from `API/ProjectiveGradedFlat.lean`, and Cohomology and Base Change from
`API/ProjectiveGradedRelativeCBC.lean`. One field, `isGloballyGenerated_of_fibres`, is still a
recorded obligation there.

NOTE (2026-08-29): before the coherence and flatness *witness* fields above were added, this
obligation was **vacuous** — no field asserted that anything was coherent or flat, so
`IsCoherent := fun _ ↦ False` satisfied the whole structure (verified in Lean) and discharging
it would have left Proposition 2.3.18 unusable. The witnesses now make a term of this
structure carry real content. See the `[erratum]` in
`StacksAndModuli/Section2.3-Regularity/COMMENTARY.md`. -/

end AlgebraicGeometry.ProjectiveSpace
