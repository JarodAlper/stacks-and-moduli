module

public import StacksAndModuli.API.TildeExact
public import StacksAndModuli.API.FlasqueVanishing
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import StacksAndModuli.API.SheafCohomologyLES
public import StacksAndModuli.API.SheafCohomologyOpenLES

/-!
# Quasicoherent sheaves on a noetherian affine scheme are acyclic

**Hartshorne III.3.5.**  For a noetherian ring `R` and any `R`-module `M`,

`Hⁱ(Spec R, M̃) = 0` for every `i ≥ 1`.

The proof is the dimension shift along an injective resolution of `M` *in `ModuleCat R`*:

* `~` is exact (`AlgebraicGeometry.tilde.shortExact_tilde_map`), so
  `0 → M ↪ I ↠ Q → 0` becomes a short exact sequence of sheaves;
* `Ĩ` is flasque (`AlgebraicGeometry.tilde.isFlasque_tilde`, Hartshorne III.3.4), hence
  `Hᵏ⁺¹(Spec R, Ĩ) = 0` by `TopCat.Sheaf.subsingleton_H_of_isFlasque`;
* `Γ(Spec R, Ĩ) = I ↠ Q = Γ(Spec R, Q̃)`, so `H¹(M̃) = 0`
  (`Scheme.Modules.subsingleton_H_one_of_shortExact_of_surjective_appTop`);
* `Hᵏ⁺²(M̃) ≅ Hᵏ⁺¹(Q̃)`, which is the induction hypothesis for `Q` — legitimate because the
  statement is proved for *all* modules simultaneously, and `Q̃` is again a tilde.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry PrimeSpectrum Limits

namespace AlgebraicGeometry.tilde

variable {R : CommRingCat.{u}} [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- An injective object of `ModuleCat R` is a Baer module. -/
lemma baer_of_injective (I : ModuleCat.{u} R) [CategoryTheory.Injective I] :
    Module.Baer R I := by
  have h : CategoryTheory.Injective (ModuleCat.of R (I : Type u)) :=
    inferInstanceAs (CategoryTheory.Injective I)
  have := Module.injective_module_of_injective_object (R : Type u) (I : Type u)
  exact Module.Baer.of_injective this

/-- The short exact sequence `0 → M → I → Q → 0` given by an injective embedding of `M`. -/
noncomputable def injSC (M : ModuleCat.{u} R) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _)

omit [IsNoetherianRing R] in
lemma injSC_shortExact (M : ModuleCat.{u} R) : (injSC M).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := Injective.ι_mono M
  epi_g := coequalizer.π_epi

/-- Its image under `~`: a short exact sequence of sheaves of modules on `Spec R` whose middle
term is flasque. -/
noncomputable abbrev tildeInjSC (M : ModuleCat.{u} R) : ShortComplex ((Spec R).Modules) :=
  haveI : (tilde.functor R).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  (injSC M).map (tilde.functor R)

lemma tildeInjSC_shortExact (M : ModuleCat.{u} R) : (tildeInjSC M).ShortExact :=
  shortExact_tilde_map (injSC_shortExact M)

lemma isFlasque_tildeInjSC_X₂ (M : ModuleCat.{u} R) :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tildeInjSC M).X₂) :=
  isFlasque_tilde _ (baer_of_injective (Injective.under M))

lemma subsingleton_H_tildeInjSC_X₂ (M : ModuleCat.{u} R) (m : ℕ) :
    Subsingleton
      (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tildeInjSC M).X₂).H (m + 1)) :=
  Scheme.Modules.subsingleton_H_of_isFlasque _ (isFlasque_tildeInjSC_X₂ M) m

omit [IsNoetherianRing R] in
lemma surjective_tildeInjSC_g (M : ModuleCat.{u} R) :
    Function.Surjective ((tildeInjSC M).g.val.app (op ⊤)).hom :=
  surjective_mapApp_top (cokernel.π (Injective.ι M))
    ((ModuleCat.epi_iff_surjective _).mp coequalizer.π_epi)

/-- **Quasicoherent sheaves on a noetherian affine scheme are acyclic** (Hartshorne III.3.5). -/
theorem subsingleton_H_tilde (n : ℕ) (M : ModuleCat.{u} R) :
    Subsingleton (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tilde M)).H (n + 1)) := by
  induction n generalizing M with
  | zero =>
      exact Scheme.Modules.subsingleton_H_one_of_shortExact_of_surjective_appTop
        (tildeInjSC_shortExact M) (surjective_tildeInjSC_g M)
        (subsingleton_H_tildeInjSC_X₂ M 0)
  | succ k ih =>
      exact AlgebraicGeometry.subsingleton_H_of_shortExact_left
        (Scheme.Modules.shortExact_map_toSheaf (tildeInjSC_shortExact M))
        (n₀ := k + 1) (n₁ := k + 2) rfl
        (ih (cokernel (Injective.ι M))) (subsingleton_H_tildeInjSC_X₂ M (k + 1))

/-- **Every quasicoherent sheaf on `Spec R` is acyclic**, `R` noetherian.  This is the form
the Čech-to-derived comparison on `ℙⁿ` consumes: `M ≅ Γ(M)~` for `M` quasicoherent, and
cohomology only sees the isomorphism class. -/
theorem subsingleton_H_of_isQuasicoherent (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M).H (n + 1)) :=
  Scheme.Modules.subsingleton_H_of_iso (asIso M.fromTildeΓ) (n + 1)
    (subsingleton_H_tilde n _)

/-! ## Acyclicity on a basic open

The same induction run at a fixed basic open `D(f)` instead of at `⊤`.  Nothing has to be
transported along `D(f) ≅ Spec R_f`: the sections of `Ĩ` and `Q̃` over `D(f)` are `I_f` and
`Q_f`, and `I_f ↠ Q_f` because localization is right exact.  This is the form the
Mayer–Vietoris computation over an affine cover consumes. -/

omit [IsNoetherianRing R] in
lemma surjective_tildeInjSC_g_basicOpen (M : ModuleCat.{u} R) (f : R) :
    Function.Surjective
      (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).map (tildeInjSC M).g).hom.app
        (op (basicOpen f))) :=
  surjective_mapApp_basicOpen (cokernel.π (Injective.ι M))
    ((ModuleCat.epi_iff_surjective _).mp coequalizer.π_epi) f

lemma subsingleton_HPrime_tildeInjSC_X₂ (M : ModuleCat.{u} R) (m : ℕ)
    (U : Opens (PrimeSpectrum R)) :
    Subsingleton
      (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tildeInjSC M).X₂).H' (m + 1) U) := by
  have hfl := isFlasque_tildeInjSC_X₂ M
  exact CategoryTheory.Sheaf.subsingleton_HPrime_succ_of_isFlasque m
    ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tildeInjSC M).X₂) U

/-- **`Hⁱ(D(f), M̃) = 0` for `i ≥ 1`**, the site-local form of Hartshorne III.3.5. -/
theorem subsingleton_HPrime_tilde (n : ℕ) (M : ModuleCat.{u} R) (f : R) :
    Subsingleton
      (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tilde M)).H' (n + 1)
        (basicOpen f)) := by
  induction n generalizing M with
  | zero =>
      exact CategoryTheory.Sheaf.subsingleton_HPrime_one_of_shortExact_of_surjective
        (Scheme.Modules.shortExact_map_toSheaf (tildeInjSC_shortExact M)) _
        (surjective_tildeInjSC_g_basicOpen M f)
        (subsingleton_HPrime_tildeInjSC_X₂ M 0 _)
  | succ k ih =>
      exact CategoryTheory.Sheaf.subsingleton_HPrime_succ_of_shortExact
        (Scheme.Modules.shortExact_map_toSheaf (tildeInjSC_shortExact M)) _ k
        (ih (cokernel (Injective.ι M)))
        (subsingleton_HPrime_tildeInjSC_X₂ M (k + 1) _)

/-- **Every quasicoherent sheaf on `Spec R` is acyclic on every basic open.** -/
theorem subsingleton_HPrime_of_isQuasicoherent
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ) (f : R) :
    Subsingleton
      (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M).H' (n + 1) (basicOpen f)) := by
  have hiso : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact CategoryTheory.Sheaf.subsingleton_HPrime_of_iso
    ((SheafOfModules.toSheaf _).mapIso (asIso M.fromTildeΓ)) (n + 1) _
    (subsingleton_HPrime_tilde n _ f)

end AlgebraicGeometry.tilde
