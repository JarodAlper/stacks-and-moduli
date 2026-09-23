module

public import StacksAndModuli.API.QuasicoherentSectionsCriterion
public import StacksAndModuli.API.QuasicoherentSectionsQcqs
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Pushforward along a qcqs morphism preserves quasicoherence

Mathlib knows that pushforward preserves quasicoherence along an *affine* morphism
(`API/AffinePushforwardQuasicoherent.lean`) and along an open immersion
(`Scheme.Modules.isQuasicoherent_restrictFunctor`).  Neither covers the projection
`π : ℙⁿ_S → S`, which is the pushforward that the Grassmannian embedding of `Quot` needs:
`π` is proper, not affine.

The general statement holds for any quasi-compact quasi-separated `f`, and the proof is
short once the two halves are in place:

* `API/QuasicoherentSectionsQcqs.lean` shows that a quasicoherent sheaf's sections
  localize on a **qcqs open** — annihilation and clearing of denominators;
* `API/QuasicoherentSectionsCriterion.lean` shows that those two conditions, on affine
  opens, *characterize* quasicoherence.

For `f` qcqs the preimage of an affine open is qcqs, so the first result feeds the second
directly.  Everything else is bookkeeping: `Γ(f_*N, V)` is definitionally `Γ(N, f ⁻¹ᵁ V)`,
the `Γ(Y,V)`-action on it is definitionally restriction of scalars along `f.app V`, and
`f ⁻¹ᵁ Y.basicOpen r = X.basicOpen (f.app U r)` matches the two basic opens up to an
equality of opens that `subst` removes.  The scalar comparison across that equality is
`Scheme.Hom.map_appLE`, the naturality of `f.app` in the open.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward_of_qcqs`.
-/

@[expose] public section

noncomputable section

-- These options are load-bearing throughout the library.
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- **Pushforward along a quasi-compact quasi-separated morphism preserves
quasicoherence.**

The preimage of an affine open under a qcqs morphism is a qcqs open, where sections of a
quasicoherent sheaf localize; that is exactly the input of
`Scheme.Modules.isQuasicoherent_of_sections_localization`. -/
instance isQuasicoherent_pushforward_of_qcqs {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (N : X.Modules) [N.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj N).IsQuasicoherent := by
  apply Scheme.Modules.isQuasicoherent_of_sections_localization
  · intro U r z hz
    have hcpt : IsCompact ((f ⁻¹ᵁ U.1 : X.Opens) : Set X) :=
      f.isCompact_preimage U.2.isCompact
    have key : ∀ (W : X.Opens) (hW : W ≤ f ⁻¹ᵁ U.1) (_hWeq : W = f ⁻¹ᵁ Y.basicOpen r),
        (N.presheaf.map (homOfLE hW).op).hom z = 0 := by
      intro W hW hWeq
      subst hWeq
      exact hz
    obtain ⟨n, hn⟩ :=
      Scheme.Modules.exists_pow_smul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
        N hcpt (f.app U.1 r) z (key _ _ (Scheme.preimage_basicOpen f r).symm)
    refine ⟨n, ?_⟩
    change (f.app U.1 (r ^ n)) • (show Γ(N, f ⁻¹ᵁ U.1) from z) = 0
    rw [map_pow]
    exact hn
  · intro U r z
    have hcpt : IsCompact ((f ⁻¹ᵁ U.1 : X.Opens) : Set X) :=
      f.isCompact_preimage U.2.isCompact
    have hqs : IsQuasiSeparated ((f ⁻¹ᵁ U.1 : X.Opens) : Set X) :=
      f.isQuasiSeparated_preimage U.2.isQuasiSeparated
    have key : ∀ (W : X.Opens) (hWle : W ≤ f ⁻¹ᵁ U.1)
        (_hWeq : W = X.basicOpen (f.app U.1 r)) (w : Γ(N, W)) (sc : Γ(X, W))
        (_hsc : sc = (X.presheaf.map (homOfLE hWle).op).hom (f.app U.1 r)),
        ∃ (z₀ : Γ(N, f ⁻¹ᵁ U.1)) (n : ℕ),
          (N.presheaf.map (homOfLE hWle).op).hom z₀ = sc ^ n • w := by
      intro W hWle hWeq w sc hsc
      subst hWeq
      subst hsc
      exact Scheme.Modules.exists_pow_smul_res_of_basicOpen_of_qcqs N hcpt hqs
        (f.app U.1 r) w
    obtain ⟨z₀, n, hn⟩ := key (f ⁻¹ᵁ Y.basicOpen r)
      (fun _ hx => Y.basicOpen_le r hx) (Scheme.preimage_basicOpen f r) z _ rfl
    have hsc : f.app (Y.basicOpen r)
          ((Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom r) =
        (X.presheaf.map (homOfLE (fun _ hx => Y.basicOpen_le r hx :
          f ⁻¹ᵁ Y.basicOpen r ≤ f ⁻¹ᵁ U.1)).op).hom (f.app U.1 r) := by
      simpa only [CommRingCat.comp_apply, Scheme.Hom.appLE, homOfLE_refl, op_id,
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using
        ConcreteCategory.congr_hom (Scheme.Hom.map_appLE f
          (le_rfl : f ⁻¹ᵁ Y.basicOpen r ≤ f ⁻¹ᵁ Y.basicOpen r)
          (homOfLE (Y.basicOpen_le r)).op) r
    refine ⟨z₀, n, ?_⟩
    change (N.presheaf.map (homOfLE (fun _ hx => Y.basicOpen_le r hx :
        f ⁻¹ᵁ Y.basicOpen r ≤ f ⁻¹ᵁ U.1)).op).hom z₀ =
      f.app (Y.basicOpen r) ((Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom r ^ n) •
        (show Γ(N, f ⁻¹ᵁ Y.basicOpen r) from z)
    rw [map_pow, hsc]
    exact hn

end AlgebraicGeometry.Scheme.Modules
