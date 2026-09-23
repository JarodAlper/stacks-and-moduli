module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# Detecting epimorphisms of quasicoherent modules on affine schemes

For quasicoherent module sheaves on `Spec R`, a morphism is an epimorphism if and only if
its map on global sections is surjective.  The nontrivial detection direction follows from
the tilde--global-sections equivalence: a surjective module map is an epimorphism, tilde
preserves epimorphisms, and the tilde--global-sections counit is an isomorphism on
quasicoherent modules.

Both the `moduleSpecΓFunctor` formulation and the directly usable top-open formulation are
provided.  Transport along the canonical isomorphism of an affine scheme with its spectrum
then gives an affine-scheme version and a criterion for epimorphisms after restriction to an
affine open.

Main declarations:

* `AlgebraicGeometry.Scheme.Modules.epi_of_moduleSpecΓFunctor_map_surjective`;
* `AlgebraicGeometry.Scheme.Modules.epi_of_appTop_surjective`;
* `AlgebraicGeometry.Scheme.Modules.epi_iff_moduleSpecΓFunctor_map_surjective`;
* `AlgebraicGeometry.Scheme.Modules.epi_iff_appTop_surjective`;
* `AlgebraicGeometry.Scheme.Modules.epi_of_appTop_surjective_of_isAffine`;
* `AlgebraicGeometry.Scheme.Modules.epi_iff_appTop_surjective_of_isAffine`;
* `AlgebraicGeometry.Scheme.Modules.epi_restrictFunctor_map_of_app_image_top_surjective`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}}

/-- An epimorphism of quasicoherent sheaves on an affine spectrum splits when
its target module of global sections is projective.  This is the sheaf form of
the lifting property for projective modules, transported through the
tilde--global-sections equivalence. -/
theorem isSplitEpi_of_epi_of_projective_globalSections
    {F G : (Spec R).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (p : F ⟶ G) [Epi p]
    [Module.Projective R (moduleSpecΓFunctor.obj G)] : IsSplitEpi p := by
  let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
  let F' : P.FullSubcategory := ⟨F, inferInstance⟩
  let G' : P.FullSubcategory := ⟨G, inferInstance⟩
  let p' : F' ⟶ G' := ⟨p⟩
  let E := tildeEquiv (R := R)
  letI : Epi p' := by
    constructor
    intro Z f g h
    apply ObjectProperty.hom_ext
    apply (cancel_epi p).mp
    exact congrArg (fun k ↦ k.hom) h
  letI : Epi (E.inverse.map p') := inferInstance
  have hproj : Module.Projective R (E.inverse.obj G') := by
    change Module.Projective R (moduleSpecΓFunctor.obj G)
    infer_instance
  letI : Module.Projective R (E.inverse.obj G') := hproj
  letI : CategoryTheory.Projective (E.inverse.obj G') :=
    ModuleCat.projective_of_categoryTheory_projective _
  let sCat : E.inverse.obj G' ⟶ E.inverse.obj F' :=
    Projective.factorThru (𝟙 _) (E.inverse.map p')
  have hs : sCat ≫ E.inverse.map p' = 𝟙 _ :=
    Projective.factorThru_comp (𝟙 _) (E.inverse.map p')
  let s' : G' ⟶ F' := E.inverse.preimage sCat
  have hs' : s' ≫ p' = 𝟙 G' := by
    apply E.inverse.map_injective
    rw [E.inverse.map_comp, E.inverse.map_preimage, E.inverse.map_id]
    exact hs
  exact IsSplitEpi.mk' {
    section_ := s'.hom
    id := congrArg (fun k : G' ⟶ G' ↦ k.hom) hs' }

/-- A morphism of quasicoherent module sheaves on an affine spectrum is an epimorphism if
its image under the affine global-sections functor is surjective. -/
theorem epi_of_moduleSpecΓFunctor_map_surjective
    {F G : (Spec R).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (p : F ⟶ G) (hp : Function.Surjective (moduleSpecΓFunctor.map p)) : Epi p := by
  haveI hΓ : Epi (moduleSpecΓFunctor.map p) :=
    (ModuleCat.epi_iff_surjective _).mpr hp
  haveI htilde : Epi ((tilde.functor R).map (moduleSpecΓFunctor.map p)) := inferInstance
  haveI hF : IsIso F.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent F
  haveI hG : IsIso G.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent G
  have hnat : (tilde.functor R).map (moduleSpecΓFunctor.map p) ≫ G.fromTildeΓ =
      F.fromTildeΓ ≫ p := by
    exact fromTildeΓNatTrans.naturality p
  constructor
  intro Z f g h
  apply (cancel_epi
    ((tilde.functor R).map (moduleSpecΓFunctor.map p) ≫ G.fromTildeΓ)).mp
  rw [hnat, Category.assoc, Category.assoc, h]

/-- A morphism of quasicoherent module sheaves on an affine spectrum is an epimorphism if
its map on sections over the top open is surjective. -/
theorem epi_of_appTop_surjective
    {F G : (Spec R).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (p : F ⟶ G) (hp : Function.Surjective (p.app ⊤).hom) : Epi p := by
  apply epi_of_moduleSpecΓFunctor_map_surjective p
  exact hp

/-- Epimorphisms of quasicoherent module sheaves on an affine spectrum are exactly the
morphisms whose affine global-sections map is surjective. -/
theorem epi_iff_moduleSpecΓFunctor_map_surjective
    {F G : (Spec R).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (p : F ⟶ G) : Epi p ↔ Function.Surjective (moduleSpecΓFunctor.map p) := by
  constructor
  · intro hp
    let P := SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf
    let F' : P.FullSubcategory := ⟨F, inferInstance⟩
    let G' : P.FullSubcategory := ⟨G, inferInstance⟩
    let p' : F' ⟶ G' := ⟨p⟩
    letI : Epi p := hp
    letI : Epi p' := by
      constructor
      intro Z f g h
      apply ObjectProperty.hom_ext
      apply (cancel_epi p).1
      exact congrArg (fun k ↦ k.hom) h
    haveI : Epi ((tildeEquiv (R := R)).inverse.map p') := inferInstance
    have hs := (ModuleCat.epi_iff_surjective
      ((tildeEquiv (R := R)).inverse.map p')).mp inferInstance
    exact hs
  · exact epi_of_moduleSpecΓFunctor_map_surjective p

/-- Epimorphisms of quasicoherent module sheaves on an affine spectrum are exactly the
morphisms which are surjective on sections over the top open. -/
theorem epi_iff_appTop_surjective
    {F G : (Spec R).Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (p : F ⟶ G) : Epi p ↔ Function.Surjective (p.app ⊤).hom := by
  exact epi_iff_moduleSpecΓFunctor_map_surjective p

/-- On an affine scheme, a morphism of quasicoherent module sheaves is an epimorphism if its
map on global sections is surjective. -/
theorem epi_of_appTop_surjective_of_isAffine
    {X : Scheme.{u}} [IsAffine X]
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (p : F ⟶ G) (hp : Function.Surjective (p.app ⊤).hom) : Epi p := by
  let e := X.isoSpec
  let q := (restrictFunctor e.inv).map p
  have hq : Function.Surjective (q.app ⊤).hom := by
    change Function.Surjective (p.app (e.inv ''ᵁ ⊤)).hom
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
    exact hp
  haveI : Epi q := epi_of_appTop_surjective q hq
  let i : restrictFunctor e.inv ⋙ restrictFunctor e.hom ≅ Functor.id X.Modules :=
    (restrictFunctorComp e.hom e.inv).symm ≪≫
      restrictFunctorCongr e.hom_inv_id ≪≫ restrictFunctorId
  letI : (restrictFunctor e.inv).Faithful := i.faithful_of_comp
  exact (restrictFunctor e.inv).epi_of_epi_map inferInstance

/-- On an arbitrary affine scheme, epimorphisms of quasicoherent module sheaves are
exactly the morphisms which are surjective on global sections. -/
theorem epi_iff_appTop_surjective_of_isAffine
    {X : Scheme.{u}} [IsAffine X]
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (p : F ⟶ G) : Epi p ↔ Function.Surjective (p.app ⊤).hom := by
  constructor
  · intro hp
    let e := X.isoSpec
    let q := (restrictFunctor e.inv).map p
    letI : Epi p := hp
    haveI : Epi q := inferInstance
    have hq : Function.Surjective (q.app ⊤).hom :=
      (epi_iff_appTop_surjective q).mp inferInstance
    change Function.Surjective (p.app (e.inv ''ᵁ ⊤)).hom at hq
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso] at hq
    exact hq
  · exact epi_of_appTop_surjective_of_isAffine p

/-- Let `j : U ⟶ X` be an open immersion with affine source.  A morphism of
quasicoherent module sheaves on `X` restricts to an epimorphism on `U` if its map on
sections over the image of the top open of `U` is surjective. -/
theorem epi_restrictFunctor_map_of_app_image_top_surjective
    {U X : Scheme.{u}} [IsAffine U] (j : U ⟶ X) [IsOpenImmersion j]
    {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (p : F ⟶ G)
    (hp : Function.Surjective (p.app (j ''ᵁ ⊤)).hom) :
    Epi ((restrictFunctor j).map p) := by
  apply epi_of_appTop_surjective_of_isAffine ((restrictFunctor j).map p)
  exact hp

end AlgebraicGeometry.Scheme.Modules

end

end
