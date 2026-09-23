module

public import StacksAndModuli.API.FpqcMorphismPropertySieve
public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Target-locality for the étale precoverage

This module upgrades fpqc descent of a scheme morphism property to locality at the target
for arbitrary étale covering families.  The existing fpqc-sieve descent theorem applies
because every étale cover is a pro-étale cover, and every pro-étale cover is fpqc.

## Main declaration

- `AlgebraicGeometry.Scheme.isLocalAtTarget_etalePrecoverage_of_descendsAlong`:
  a base-change-stable, Zariski-target-local property which descends along singleton fpqc
  covers is local at the target for `Scheme.etalePrecoverage`.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable (P : MorphismProperty Scheme.{u})
variable [P.IsStableUnderBaseChange] [IsZariskiLocalAtTarget P]
variable [P.DescendsAlong
  (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})]

/-- A base-change-stable and Zariski-target-local morphism property which descends along
surjective flat quasi-compact morphisms is local at the target for arbitrary étale
covering families. -/
theorem isLocalAtTarget_etalePrecoverage_of_descendsAlong :
    P.IsLocalAtTarget etalePrecoverage := by
  let _ : etalePrecoverage.{u}.IsStableUnderBaseChange := by
    dsimp only [etalePrecoverage]
    infer_instance
  apply CategoryTheory.MorphismProperty.IsLocalAtTarget.mk_of_isStableUnderBaseChange
  intro X Y f 𝒰 h
  have h𝒰 : 𝒰.presieve₀ ∈ fpqcPrecoverage Y :=
    (etalePrecoverage_le_proetalePrecoverage.trans
      proetalePrecoverage_le_fpqcPrecoverage) Y 𝒰.mem₀
  apply AlgebraicGeometry.MorphismProperty.of_fpqc_sieve (P := P) f
    (Sieve.generate 𝒰.presieve₀)
    (Precoverage.generate_mem_toGrothendieck h𝒰)
  rintro V g ⟨W, k, p, ⟨i⟩, rfl⟩
  rw [← P.cancel_left_of_respectsIso
    (pullbackLeftPullbackSndIso f (𝒰.f i) k).hom,
    pullbackLeftPullbackSndIso_hom_snd]
  exact P.pullback_snd _ _ (h i)

end AlgebraicGeometry.Scheme
