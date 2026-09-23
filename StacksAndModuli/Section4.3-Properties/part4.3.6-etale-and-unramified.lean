module

public import StacksAndModuli.«Section4.3-Properties».«part4.3.5-quasi-finite-morphisms»

/-!
# Étale and unramified morphisms

This module formalizes `def:relatively-deligne-mumford` and `def:etale` and covers
`exer:diagonal-characterizations` of §4.3 (First properties) of *Stacks and Moduli*
(the section carries no `sec:` label). It
corresponds to the subsection "Étale and unramified morphisms", the last subsection of
§4.3.

Main declarations:
- `AlgebraicGeometry.BasedFunctor.RelativelyDeligneMumford`: morphisms of stacks all of
  whose base changes by schemes are Deligne–Mumford stacks;
- `AlgebraicGeometry.BasedFunctor.Etale` and
  `AlgebraicGeometry.BasedFunctor.Unramified`: étale and unramified morphisms of
  algebraic stacks, via relatively Deligne–Mumford morphisms and mixed
  smooth/étale presentations (unramifiedness of morphisms of schemes is spelled
  `@LocallyOfFiniteType ⊓ @FormallyUnramified`, as Mathlib has no bundled `Unramified`
  class);
- the characterization "étale = smooth + unramified"
  (`AlgebraicGeometry.BasedFunctor.etale_iff_smooth_and_unramified`).
-/

@[expose] public section

-- These files were written when Lean's backward-compat defeq options were on by default.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


section DefRelativelyDeligneMumford

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- **Definition 4.3.36** (`def:relatively-deligne-mumford`): a morphism of stacks
$\cX \to \cY$ over $\Sch_{\ét}$ is *relatively Deligne–Mumford* if for every morphism
$T \to \cY$ from a scheme, the fiber product $\cX \times_{\cY} T$ is a Deligne–Mumford
stack. -/
def RelativelyDeligneMumford (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  ∀ (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒴),
    IsDeligneMumfordStack (BasedCategory.fiberProduct F g)

/- LEDGER — **Definition 4.3.36** (`def:relatively-deligne-mumford`) (from the
unlabeled discussion following it): relatively
Deligne–Mumford morphisms are characterized by the unramifiedness of the diagonal
(`cor:characterization-of-relatively-DM`, §4.2); a morphism whose diagonal is locally
quasi-finite is called *quasi-DM* (Stacks 04YW). Both statements require the §4.2
diagonal — to be completed once Section4.2-Representability lands. -/

end AlgebraicGeometry.BasedFunctor

end DefRelativelyDeligneMumford


section DefEtale

open CategoryTheory AlgebraicGeometry CategoryTheory.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}} {𝒴 : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- **Definition 4.3.37** (`def:etale`) (étale morphisms): a morphism $\cX \to \cY$ of
algebraic stacks is *étale* if it is relatively Deligne–Mumford and for every smooth
presentation $V \to \cY$ and étale presentation $U \to \cX \times_{\cY} V$, the induced
morphism of schemes $U \to V$ is étale. (Étaleness of morphisms of schemes is étale
local on the source and smooth local on the target, so this is well defined on
relatively Deligne–Mumford morphisms.) -/
def Etale (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  RelativelyDeligneMumford F ∧
    HasPropertyOfPresentations
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth)
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Etale)
      (@_root_.AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) F

/-- **Definition 4.3.37** (`def:etale`) (unramified morphisms): a morphism
$\cX \to \cY$ of algebraic stacks is *unramified* if it is relatively Deligne–Mumford
and for every smooth presentation $V \to \cY$ and étale presentation
$U \to \cX \times_{\cY} V$, the induced morphism of schemes $U \to V$ is unramified,
i.e. locally of finite type and formally unramified. -/
def Unramified (F : 𝒳 ⥤ᵇ 𝒴) : Prop :=
  RelativelyDeligneMumford F ∧
    HasPropertyOfPresentations
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth)
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Etale)
      (@_root_.AlgebraicGeometry.LocallyOfFiniteType ⊓
        @_root_.AlgebraicGeometry.FormallyUnramified : MorphismProperty Scheme.{u}) F

variable [IsAlgebraicStack 𝒳] [IsAlgebraicStack 𝒴]

/-- API theorem following Definition 4.3.37 (étale = smooth and unramified, from the
unlabeled paragraph following it): a morphism of algebraic stacks is étale if and only
if it is smooth and unramified. (This follows from the analogous facts for morphisms of
schemes, Theorems A.3.1 and A.3.3 of Appendix A.3.) -/
theorem etale_iff_smooth_and_unramified (F : 𝒳 ⥤ᵇ 𝒴) :
    Etale F ↔ (Smooth F ∧ Unramified F) := by
  constructor
  · rintro ⟨hrel, hEtale⟩
    refine ⟨?_, ⟨hrel, ?_⟩⟩
    · apply hasProperty_of_exists isSmoothLocal_smooth
      obtain ⟨V, g, hg⟩ := IsAlgebraicStack.exists_presentation (𝒳 := 𝒴)
      let _ : IsDeligneMumfordStack (BasedCategory.fiberProduct F g) := hrel V g
      obtain ⟨U, q, hq⟩ :=
        IsDeligneMumfordStack.exists_presentation
          (𝒳 := BasedCategory.fiberProduct F g)
      refine ⟨V, g, hg, U, q,
        hq.mono (inf_le_inf le_rfl etale_le_smooth), ?_⟩
      exact etale_le_smooth _ _ _ (hEtale V g hg U q hq)
    · intro V g hg U q hq
      let f := (q.comp (BasedCategory.fiberProductSnd F g)).overHom
      have hf : _root_.AlgebraicGeometry.Etale f := hEtale V g hg U q hq
      let _ : _root_.AlgebraicGeometry.Etale f := hf
      exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hSmooth, hrel, hUnramified⟩
    refine ⟨hrel, ?_⟩
    intro V g hg U q hq
    let f := (q.comp (BasedCategory.fiberProductSnd F g)).overHom
    have hfSmooth : _root_.AlgebraicGeometry.Smooth f :=
      hSmooth V g hg U q (hq.mono (inf_le_inf le_rfl etale_le_smooth))
    have hfUnramified := hUnramified V g hg U q hq
    let _ : _root_.AlgebraicGeometry.Smooth f := hfSmooth
    let _ : _root_.AlgebraicGeometry.FormallyUnramified f := hfUnramified.2
    exact _root_.AlgebraicGeometry.Etale.of_formallyUnramified_of_flat f

/- LEDGER — **Definition 4.3.37** (`def:etale`) (from the unlabeled discussion
following it):
- a morphism is unramified if and only if its diagonal is étale — requires the §4.2
  diagonal, to be completed once Section4.2-Representability lands;
- étale morphisms are smooth and locally quasi-finite but not conversely: over a field
  of characteristic `p`, the morphism `B μ_p → Spec k` is smooth and quasi-finite but
  not étale, since `B μ_p` is not Deligne–Mumford (`exer:Bmu_n`); similarly étale
  morphisms are smooth of relative dimension `0` but not conversely, e.g.
  `B μ_p → Spec k` in characteristic `p` or `[𝔸¹/𝔾_m] → Spec k` in any characteristic.
  Blocked on classifying and quotient stacks (§3.4/§3.5 ledgers). -/

end AlgebraicGeometry.BasedFunctor

end DefEtale


section ExerDiagonalCharacterizations

/- Relocation note for Exercise 4.3.38: it is formalized **in
`StacksAndModuli/Section4.8-Properness/part4.8.1-definitions.lean`**, in the section block
`ExerDiagonalCharacterizations`: `tfae_unramified_diag`,
`tfae_isSeparatedRepresentable_diag` and `tfae_quasiSeparated_diag` (statements; the
proofs are recorded obligations). It is stated there rather than here because two of its
three variants speak about separatedness and quasi-separatedness of the diagonal, which
are §4.8 vocabulary (`BasedFunctor.IsSeparatedRepresentable`, `BasedFunctor.QuasiSeparated`
— themselves parts (4) and (2) of Definition 4.3.11, also formalized there). The relative
inertia `I_{𝒳/𝒴}` and the double diagonal are `CategoryTheory.BasedFunctor.inertia` and
`…inertiaUnit` of §4.2 (`exer:relative-inertia-properties`). Compare Stacks 0CL0. -/

end ExerDiagonalCharacterizations
