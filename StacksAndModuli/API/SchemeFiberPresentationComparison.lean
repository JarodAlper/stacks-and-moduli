module

public import StacksAndModuli.API.PresentationBaseChange
public import StacksAndModuli.API.PrestackFiberProductAssoc

/-!
# Comparing scheme presentations of prestack fibers

A scheme representation of a prestack fiber can be pulled back along a map of
base schemes.  Any two scheme representations of the same prestack differ by
an isomorphism of their representing schemes, compatibly with their structural
maps to a fixed base.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Limits AlgebraicGeometry
open CategoryTheory.BasedCategory

universe v₂ v₃ u₂ u₃ u

namespace AlgebraicGeometry.BasedFunctor

/-- Base change of a scheme representation of a prestack fiber, with its
structural map identified with the ordinary pullback projection. -/
theorem exists_baseChange_scheme_representation
    {Xcat : BasedCategory.{v₂, u₂} Scheme.{u}}
    {Ycat : BasedCategory.{v₃, u₃} Scheme.{u}}
    [Xcat.p.IsFiberedInGroupoids] [Ycat.p.IsFiberedInGroupoids]
    {F : Xcat ⥤ᵇ Ycat} {T U S : Scheme.{u}}
    {g : overBased T ⥤ᵇ Ycat}
    (E : overBased U ⥤ᵇ fiberProduct F g)
    (hE : E.toFunctor.IsEquivalence) (p : S ⟶ T) :
    ∃ E' : overBased
        (pullback (E.comp (fiberProductSnd F g)).overHom p) ⥤ᵇ
          fiberProduct F ((overBased.map p).comp g),
      E'.toFunctor.IsEquivalence ∧
        (E'.comp (fiberProductSnd F
          ((overBased.map p).comp g))).overHom =
          pullback.snd (E.comp (fiberProductSnd F g)).overHom p := by
  let _ : E.toFunctor.IsEquivalence := hE
  let A := E.comp (fiberProductSnd F g)
  let L₀ := overBasedFiberPullbackEquivalence A p
  let _ : L₀.toFunctor.IsEquivalence :=
    isEquivalence_overBasedFiberPullbackEquivalence A p
  let L₁ := fiberProductLeftMap (fiberProductSnd F g)
    (overBased.map p) E
  let _ : L₁.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductLeftMap (fiberProductSnd F g)
      (overBased.map p) E
  let L₂ := fiberProductAssoc F g (overBased.map p)
  let _ : L₂.toFunctor.IsEquivalence :=
    isEquivalence_fiberProductAssoc F g (overBased.map p)
  let E' := (L₀.comp L₁).comp L₂
  have hL₀L₁ : (L₀.comp L₁).toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans L₀.toFunctor L₁.toFunctor
  have hE' : E'.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans (L₀.comp L₁).toFunctor L₂.toFunctor
  refine ⟨E', hE', ?_⟩
  have hL₁snd : L₁.comp
      (fiberProductSnd (fiberProductSnd F g) (overBased.map p)) =
      fiberProductSnd A (overBased.map p) := by
    apply CategoryTheory.BasedFunctor.ext_of_toFunctor_eq
    rfl
  rw [show E'.comp (fiberProductSnd F ((overBased.map p).comp g)) =
      L₀.comp (fiberProductSnd A (overBased.map p)) by
    simp only [E', L₂, CategoryTheory.BasedFunctor.comp_assoc,
      fiberProductAssoc_comp_snd, hL₁snd]]
  simpa only [L₀, A, CategoryTheory.BasedFunctor.overHom_map] using
    congrArg CategoryTheory.BasedFunctor.overHom
      (overBasedFiberPullbackEquivalence_comp_snd A p)

/-- Two scheme representations of one prestack are related by an isomorphism
of the representing schemes, and the induced structural maps agree after that
isomorphism. -/
theorem exists_isIso_overHom_comp_eq_of_scheme_representations
    {Zcat : BasedCategory.{v₂, u₂} Scheme.{u}}
    [Zcat.p.IsFiberedInGroupoids]
    {S U V : Scheme.{u}}
    (E : overBased U ⥤ᵇ Zcat) (hE : E.toFunctor.IsEquivalence)
    (K : overBased V ⥤ᵇ Zcat) (hK : K.toFunctor.IsEquivalence)
    (q : Zcat ⥤ᵇ overBased S) :
    ∃ f : V ⟶ U, CategoryTheory.IsIso f ∧
      f ≫ (E.comp q).overHom = (K.comp q).overHom := by
  let _ : E.toFunctor.IsEquivalence := hE
  let _ : K.toFunctor.IsEquivalence := hK
  obtain ⟨J, ⟨α⟩, ⟨β⟩⟩ :=
    CategoryTheory.BasedFunctor.exists_inverse_of_toFunctor E
  let _ : J.toFunctor.IsEquivalence :=
    Functor.IsEquivalence.mk' E.toFunctor
      ((BasedNatTrans.forgetful _ _).mapIso β).symm
      ((BasedNatTrans.forgetful _ _).mapIso α)
  let H := K.comp J
  have hH : H.toFunctor.IsEquivalence :=
    Functor.isEquivalence_trans K.toFunctor J.toFunctor
  let f : V ⟶ U := H.overHom
  have hf : CategoryTheory.IsIso f :=
    CategoryTheory.BasedFunctor.isIso_overHom_of_isEquivalence H hH
  obtain ⟨eH⟩ := CategoryTheory.BasedFunctor.nonempty_iso_overBased_map H
  let e : (overBased.map f).comp E ≅ K :=
    (isoWhiskerRight eH.symm E).trans
      ((eqToIso (CategoryTheory.BasedFunctor.comp_assoc K J E)).trans
        ((isoWhiskerLeft K β).trans
          (eqToIso (CategoryTheory.BasedFunctor.comp_id K))))
  let eq : (overBased.map f).comp (E.comp q) ≅ K.comp q := by
    simpa only [CategoryTheory.BasedFunctor.comp_assoc] using
      isoWhiskerRight e q
  have hover := CategoryTheory.BasedFunctor.overHom_eq_of_iso eq
  refine ⟨f, hf, ?_⟩
  simpa only [CategoryTheory.BasedFunctor.overHom_comp,
    CategoryTheory.BasedFunctor.overHom_map] using hover

end AlgebraicGeometry.BasedFunctor
