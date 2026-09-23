module

public import StacksAndModuli.API.InjectiveSheafFlasque
public import StacksAndModuli.API.SheafCohomologyLES
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Flasque sheaves have vanishing higher cohomology

For an abelian sheaf `F` on a topological space, `Hⁿ(X, F) = 0` for all `n ≥ 1` as soon as
`F` is flasque. This is the first computational input of sheaf cohomology: it is what makes
flasque (and, downstream, injective and soft) resolutions usable, and it is the standard
route to Grothendieck vanishing and to the comparison with Čech cohomology.

The proof is the classical dimension shift. Embed `F` in an injective sheaf `I`; then

* `I` is flasque (`TopCat.Sheaf.isFlasque_of_injective`, proved in
  `StacksAndModuli/API/InjectiveSheafFlasque.lean`), hence so is the quotient `Q = I/F`
  (Mathlib's `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`);
* `H¹(F) = 0` because `Γ(I) ⟶ Γ(Q)` is surjective — this is Mathlib's
  `TopCat.Sheaf.IsFlasque.epi_of_shortExact`, read through `CategoryTheory.Sheaf.H.equiv₀`
  — so the connecting map `H⁰(Q) ⟶ H¹(F)` is both zero and surjective;
* `Hⁿ⁺²(F) ≅ Hⁿ⁺¹(Q) = 0` by induction, since `Hⁱ(I) = 0` for `i ≥ 1`.

## Main results

* `TopCat.Sheaf.surjective_H_map_zero_of_isFlasque`: `H⁰` of the quotient map is surjective
  for a short exact sequence with flasque sub.
* `TopCat.Sheaf.subsingleton_H_of_isFlasque`: **`Hⁿ⁺¹(X, F) = 0` for `F` flasque.**
* `TopCat.Sheaf.subsingleton_H_skyscraperSheaf`: skyscraper sheaves are acyclic.
* `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_isFlasque`: the same for an
  `𝒪_X`-module with flasque underlying abelian sheaf.
* `TopCat.Sheaf.isFlasque_of_subsingleton` and
  `…subsingleton_H_of_subsingleton`: every sheaf on a space with at most one point is
  flasque, hence acyclic.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

universe w

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace TopCat.Sheaf

variable {X : TopCat.{w}}

/-- For a short exact sequence of abelian sheaves whose sub is flasque, the induced map on
`H⁰` is surjective.

`H⁰` is global sections (`CategoryTheory.Sheaf.H.equiv₀` at the terminal open `⊤`), and
surjectivity on global sections is Mathlib's `TopCat.Sheaf.IsFlasque.epi_of_shortExact`. -/
lemma surjective_H_map_zero_of_isFlasque
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{w} X)} (hS : S.ShortExact)
    [S.X₁.IsFlasque] : Function.Surjective (CategoryTheory.Sheaf.H.map S.g 0) := by
  intro y
  have hepi : Epi (S.g.1.app (op (⊤ : Opens X))) :=
    TopCat.Sheaf.IsFlasque.epi_of_shortExact hS
  rw [AddCommGrpCat.epi_iff_surjective] at hepi
  obtain ⟨a, ha⟩ := hepi (CategoryTheory.Sheaf.H.equiv₀ S.X₃ Limits.isTerminalTop y)
  obtain ⟨x, rfl⟩ : ∃ x, CategoryTheory.Sheaf.H.equiv₀ S.X₂ Limits.isTerminalTop x = a :=
    ⟨(CategoryTheory.Sheaf.H.equiv₀ S.X₂ Limits.isTerminalTop).symm a, by simp⟩
  refine ⟨x, (CategoryTheory.Sheaf.H.equiv₀ S.X₃ Limits.isTerminalTop).injective ?_⟩
  rw [← CategoryTheory.Sheaf.H.equiv₀_naturality]
  exact ha

/-- The connecting map `H⁰(X₃) ⟶ H¹(X₁)` of a short exact sequence with flasque sub is
zero, and — when `H¹(X₂)` vanishes — surjective; so `H¹(X₁)` vanishes. -/
lemma subsingleton_H_one_of_isFlasque
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{w} X)} (hS : S.ShortExact)
    [S.X₁.IsFlasque] (h₂ : Subsingleton (S.X₂.H 1)) : Subsingleton (S.X₁.H 1) := by
  have hex₁ := Abelian.Ext.covariant_sequence_exact₁' (constantIntSheaf X) hS 0 1 rfl
  have hex₃ := Abelian.Ext.covariant_sequence_exact₃' (constantIntSheaf X) hS 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at hex₁ hex₃
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨y, rfl⟩ := (hex₁ x).mp (Subsingleton.elim _ _)
  exact (hex₃ y).mpr (surjective_H_map_zero_of_isFlasque hS y)

variable (F : TopCat.Sheaf AddCommGrpCat.{w} X)

/-- The short exact sequence `0 ⟶ F ⟶ I ⟶ I/F ⟶ 0` embedding an abelian sheaf in an
injective one. -/
noncomputable abbrev injectiveSES : ShortComplex (TopCat.Sheaf AddCommGrpCat.{w} X) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (by simp)

lemma injectiveSES_shortExact : (injectiveSES F).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := Injective.ι_mono F
  epi_g := coequalizer.π_epi

instance : (injectiveSES F).X₂.IsFlasque := isFlasque_of_injective _

instance [F.IsFlasque] : (injectiveSES F).X₃.IsFlasque :=
  TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ (injectiveSES_shortExact F)

/-- **Flasque sheaves have vanishing higher cohomology**: `Hⁿ⁺¹(X, F) = 0` for every
flasque abelian sheaf `F` on a topological space `X`. -/
theorem subsingleton_H_of_isFlasque (n : ℕ) (G : TopCat.Sheaf AddCommGrpCat.{w} X)
    [G.IsFlasque] : Subsingleton (G.H (n + 1)) := by
  induction n generalizing G with
  | zero =>
    exact subsingleton_H_one_of_isFlasque (injectiveSES_shortExact G) inferInstance
  | succ n ih =>
    exact AlgebraicGeometry.subsingleton_H_of_shortExact_left
      (injectiveSES_shortExact G) (n₀ := n + 1) (n₁ := n + 2) rfl (ih _) inferInstance

/-- On a space with at most one point every open is `⊥` or `⊤`. -/
lemma eq_bot_or_eq_top_of_subsingleton [Subsingleton X] (U : Opens X) : U = ⊥ ∨ U = ⊤ := by
  rcases Set.eq_empty_or_nonempty (U : Set X) with h | ⟨x, hx⟩
  · exact Or.inl (Opens.ext (by simpa using h))
  · refine Or.inr (Opens.ext ?_)
    refine Set.eq_univ_of_forall fun y ↦ ?_
    rwa [Subsingleton.elim y x]

/-- **On a space with at most one point every abelian sheaf is flasque.** The only opens are
`⊥` and `⊤`; sections over `⊥` form a terminal, hence zero, group, so every map into them is
an epimorphism, and the only other restriction map is the identity. -/
instance isFlasque_of_subsingleton [Subsingleton X]
    (F : TopCat.Sheaf AddCommGrpCat.{w} X) : F.IsFlasque where
  epi {U V} i := by
    rcases eq_bot_or_eq_top_of_subsingleton V.unop with hV | hV
    · obtain rfl : V = op ⊥ := Opposite.unop_injective hV
      have hz : Limits.IsZero (F.obj.obj (op (⊥ : Opens X))) :=
        Limits.IsZero.of_iso (Limits.isZero_zero _)
          ((TopCat.Sheaf.isTerminalOfEmpty F).uniqueUpToIso
            Limits.HasZeroObject.zeroIsTerminal)
      exact ⟨fun g h _ ↦ hz.eq_of_src g h⟩
    · obtain rfl : V = op (⊤ : Opens X) := Opposite.unop_injective hV
      obtain rfl : U = op (⊤ : Opens X) :=
        Opposite.unop_injective (top_le_iff.mp (leOfHom i.unop))
      obtain rfl : i = 𝟙 _ := Subsingleton.elim _ _
      rw [F.obj.map_id]
      infer_instance

/-- **Skyscraper sheaves have vanishing higher cohomology**, being flasque. Together with
`Hⁿ(X, F) = 0` for `n` above the dimension this is the basic computation that makes Euler
characteristics on a curve computable: adding a point to a divisor changes `χ` by the
`χ = 1` of a skyscraper. -/
instance subsingleton_H_skyscraperSheaf (p₀ : X) [∀ U : Opens X, Decidable (p₀ ∈ U)]
    (A : AddCommGrpCat.{w}) (n : ℕ) :
    Subsingleton ((skyscraperSheaf p₀ A).H (n + 1)) :=
  haveI := isFlasque_skyscraperSheaf_of_hasZeroObject p₀ A
  subsingleton_H_of_isFlasque n _

/-- **Cohomology on a space with at most one point vanishes** in positive degrees, for every
abelian sheaf. This is the smallest case of the vanishing theorems, and the one that makes
the invariants of `Spec k` come out right. -/
theorem subsingleton_H_of_subsingleton [Subsingleton X]
    (F : TopCat.Sheaf AddCommGrpCat.{w} X) (n : ℕ) : Subsingleton (F.H (n + 1)) :=
  subsingleton_H_of_isFlasque n F

end TopCat.Sheaf

namespace AlgebraicGeometry.Scheme.Modules

/-- An `𝒪_X`-module whose underlying abelian sheaf is flasque has vanishing higher
cohomology, and so `hⁿ⁺¹(X, F) = 0` and `χ(X, F) = h⁰(X, F)`. -/
lemma subsingleton_H_of_isFlasque {X : Scheme.{w}} (F : X.Modules)
    (hF : TopCat.Sheaf.IsFlasque (show TopCat.Sheaf AddCommGrpCat.{w} X from
      (SheafOfModules.toSheaf X.ringCatSheaf).obj F)) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) (n + 1)) :=
  haveI := hF
  TopCat.Sheaf.subsingleton_H_of_isFlasque n _

/-- All higher cohomology of an `𝒪_X`-module vanishes on a scheme with at most one point,
in particular on `Spec k` for a field `k`. -/
lemma subsingleton_H_of_subsingleton {X : Scheme.{w}} [Subsingleton X] (F : X.Modules)
    (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) (n + 1)) :=
  TopCat.Sheaf.subsingleton_H_of_subsingleton _ n

end AlgebraicGeometry.Scheme.Modules
