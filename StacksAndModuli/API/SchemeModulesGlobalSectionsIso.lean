module

public import StacksAndModuli.API.GlobalSectionsOverBase
public import StacksAndModuli.API.ProjectiveTwistGlobalSections

/-!
# Global sections under an isomorphism of schemes

Pullback of sheaves of modules along an isomorphism of schemes is an equivalence of
categories.  Consequently, after identifying the pulled-back sheaf with a target sheaf,
the adjunction-unit map on global sections is an additive equivalence.  When both schemes
are regarded over the same affine base, this is an equivalence of modules over the base
ring.

The definitions here make precise the otherwise routine transport needed to compare a
sheaf on a raw pullback model of relative projective space with its transport to polynomial
`Proj`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Pullback of module sheaves along an isomorphism of schemes is an equivalence of
categories. -/
noncomputable instance pullback_isEquivalence_of_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    (pullback f).IsEquivalence := by
  apply Functor.IsEquivalence.mk' (pullback (inv f))
  · exact ((pullbackComp (inv f) f).trans
      ((pullbackCongr (by simp)).trans (pullbackId Y))).symm
  · exact (pullbackComp f (inv f)).trans
      ((pullbackCongr (by simp)).trans (pullbackId X))

/-- Pulling global sections across an isomorphism of schemes and then across a sheaf
isomorphism is an additive equivalence. -/
noncomputable def pullbackGlobalSectionsViaIsoAddEquiv
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (M : Y.Modules) {N : X.Modules}
    (e : (pullback f).obj M ≅ N) : Γ(M, ⊤) ≃+ Γ(N, ⊤) := by
  letI : IsIso (pullbackPushforwardAdjunction f).unit :=
    (pullbackPushforwardAdjunction f).unit_isIso_of_L_fully_faithful
  apply AddEquiv.ofBijective (_root_.Scheme.Modules.pullbackGlobalSectionsViaIso f M e)
  exact (ConcreteCategory.bijective_of_isIso (e.hom.app (⊤ : X.Opens))).comp
    (ConcreteCategory.bijective_of_isIso
      (((pullbackPushforwardAdjunction f).unit.app M).app (⊤ : Y.Opens)))

/-- Pullback of global sections respects the scalar action of global functions. -/
lemma pullbackGlobalSections_smul
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (r : Γ(Y, ⊤)) (m : Γ(M, ⊤)) :
    _root_.Scheme.Modules.pullbackGlobalSections f M (r • m) =
      f.appTop r • _root_.Scheme.Modules.pullbackGlobalSections f M m := by
  change ((pullbackPushforwardAdjunction f).unit.app M).app ⊤ (r • m) = _
  exact (((pullbackPushforwardAdjunction f).unit.app M).val.app (op ⊤)).hom.map_smul r m

/-- The global-sections equivalence induced by an isomorphism of schemes is linear over an
affine base.  The structure morphism of the source is written as the composite `f ≫ pY`,
which is the form directly available when transporting along `f`. -/
noncomputable def pullbackGlobalSectionsViaIsoLinearEquiv
    {X Y : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Y) [IsIso f] (pY : Y ⟶ Spec R)
    (M : Y.Modules) {N : X.Modules} (e : (pullback f).obj M ≅ N) :
    letI := globalSectionsModule pY M
    letI := globalSectionsModule (f ≫ pY) N
    Γ(M, ⊤) ≃ₗ[R] Γ(N, ⊤) := by
  letI := globalSectionsModule pY M
  letI := globalSectionsModule (f ≫ pY) N
  let a := pullbackGlobalSectionsViaIsoAddEquiv f M e
  exact
    { a with
      map_smul' := by
        intro r m
        change e.hom.app ⊤
            (_root_.Scheme.Modules.pullbackGlobalSections f M
              ((baseRingHom pY).hom r • m)) =
          (baseRingHom (f ≫ pY)).hom r •
            e.hom.app ⊤ (_root_.Scheme.Modules.pullbackGlobalSections f M m)
        rw [pullbackGlobalSections_smul]
        change e.hom.val.app (op ⊤)
            (f.appTop ((baseRingHom pY).hom r) •
              _root_.Scheme.Modules.pullbackGlobalSections f M m) = _
        rw [(e.hom.val.app (op ⊤)).hom.map_smul]
        simp [baseRingHom]
        rfl }


/-- The global-sections equivalence induced by an isomorphism of schemes, with the structure
morphism of the source given separately.

`Scheme.Modules.globalSectionsModule` depends on the chosen morphism to the affine base, so
the composite `f ≫ pY` produced by `pullbackGlobalSectionsViaIsoLinearEquiv` is often not the
morphism one wants to carry downstream even when the two are propositionally equal.  This
variant takes the intended `pX` together with the identification. -/
noncomputable def pullbackGlobalSectionsViaIsoLinearEquiv'
    {X Y : Scheme.{u}} {R : CommRingCat.{u}}
    (f : X ⟶ Y) [IsIso f] (pY : Y ⟶ Spec R) (pX : X ⟶ Spec R) (hp : f ≫ pY = pX)
    (M : Y.Modules) {N : X.Modules} (e : (pullback f).obj M ≅ N) :
    letI := globalSectionsModule pY M
    letI := globalSectionsModule pX N
    Γ(M, ⊤) ≃ₗ[R] Γ(N, ⊤) := by
  subst hp
  exact pullbackGlobalSectionsViaIsoLinearEquiv f pY M e


end AlgebraicGeometry.Scheme.Modules
