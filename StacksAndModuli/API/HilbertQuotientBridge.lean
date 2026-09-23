module

public import StacksAndModuli.API.ClosedImmersionQuotient
public import StacksAndModuli.API.KernelIdealPullback
public import StacksAndModuli.API.QuasicoherentObjectProperties
public import StacksAndModuli.API.QuasicoherentQuotientClassification
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# The bridge between Hilbert data and quotients of the structure sheaf

A closed immersion `i : Z ⟶ X` determines the quasicoherent quotient
`i.closedQuotient = i_* 𝒪_Z` of `𝒪_X`.  This file develops the property
comparisons needed to identify flat finitely presented closed subschemes with flat
finitely presented quotients of the structure sheaf.

It also packages the uniqueness statement saying that a quasicoherent quotient of
`𝒪_X` with kernel `i.ker` is canonically isomorphic, under `𝒪_X`, to
`i.closedQuotient`.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace RingHom.FinitePresentation

/-- For a surjective map of commutative rings, finite presentation as a ring map is
equivalent to finite presentation of the target as a module over the source. -/
lemma iff_module_of_surjective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    f.FinitePresentation ↔
      @Module.FinitePresentation R S _ _ (Module.compHom S f) := by
  letI : Algebra R S := f.toAlgebra
  haveI : Module.Finite R S :=
    Module.Finite.of_surjective (Algebra.linearMap R S) hf
  change Algebra.FinitePresentation R S ↔ Module.FinitePresentation R S
  exact (Module.FinitePresentation.iff_finitePresentation_of_finite R S).symm

end RingHom.FinitePresentation

namespace AlgebraicGeometry

/-- On an affine spectrum, a quasicoherent sheaf is finitely presented exactly when
its coordinate module is finitely presented. -/
lemma Scheme.Modules.isFinitePresentation_iff_moduleSpecΓFunctor
    {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent] :
    M.IsFinitePresentation ↔
      Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := by
  constructor
  · intro hM
    letI : M.IsFinitePresentation := hM
    exact moduleSpecΓFunctor_finitePresentation_of_isFinitePresentation M
  · intro hM
    letI : Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := hM
    exact isFinitePresentation_of_moduleSpecΓFunctor M

/-- For a quasicoherent sheaf on a spectrum, finite presentation of intrinsic global
sections implies finite presentation in the coordinate-module convention. -/
lemma moduleSpecΓFunctor_finitePresentation_of_top {R : CommRingCat.{u}}
    (M : (Spec R).Modules)
    (hM : Module.FinitePresentation Γ(Spec R, ⊤) Γ(M, ⊤)) :
    Module.FinitePresentation R (moduleSpecΓFunctor.obj M) := by
  let eR := (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
  letI : RingHomInvPair (eR : Γ(Spec R, ⊤) →+* R)
      (eR.symm : R →+* Γ(Spec R, ⊤)) := RingHomInvPair.of_ringEquiv eR
  letI : RingHomInvPair (eR.symm : R →+* Γ(Spec R, ⊤))
      (eR : Γ(Spec R, ⊤) →+* R) := RingHomInvPair.of_ringEquiv eR.symm
  letI : Module.FinitePresentation Γ(Spec R, ⊤) Γ(M, ⊤) := hM
  let eM : Γ(M, ⊤) ≃ₛₗ[(eR : Γ(Spec R, ⊤) →+* R)]
      moduleSpecΓFunctor.obj M :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r m ↦ by
        change r • m = (Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom r) • m
        simp }
  exact Module.FinitePresentation.of_semilinearEquiv eR eM

/-- On an affine scheme, a quasicoherent sheaf is finitely presented exactly when
its module of global sections is finitely presented over the global function ring. -/
lemma Scheme.Modules.isFinitePresentation_iff_sections_top
    {X : Scheme.{u}} [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] :
    M.IsFinitePresentation ↔
      Module.FinitePresentation Γ(X, ⊤) Γ(M, ⊤) := by
  constructor
  · intro hM
    letI : M.IsFinitePresentation := hM
    obtain ⟨P, hP⟩ :=
      Scheme.Modules.exists_finitePresentation_of_isFinitePresentation_affine M
    letI : P.IsFinite := hP
    exact Scheme.Modules.finitePresentation_sections_top_of_presentation M P
  · intro hM
    let A := CommRingCat.of Γ(X, ⊤)
    let f : Spec A ⟶ X := X.isoSpec.inv
    let N := (Scheme.Modules.pullback f).obj M
    have him : f ''ᵁ (⊤ : (Spec A).Opens) = ⊤ := by
      rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
    have hImage : Module.FinitePresentation
        Γ(X, f ''ᵁ (⊤ : (Spec A).Opens))
        Γ(M, f ''ᵁ (⊤ : (Spec A).Opens)) :=
      Scheme.Modules.sections_finitePresentation_of_eq M ⊤ _ him.symm hM
    let eR := (f.appIso ⊤).commRingCatIsoToRingEquiv
    let eRestr := M.restrictAppIso f ⊤
    let ePull := Scheme.Modules.restrictSectionsLinearEquivPullback f M ⊤
    have hres (r : Γ(X, f ''ᵁ (⊤ : (Spec A).Opens)))
        (m : Γ(M, f ''ᵁ (⊤ : (Spec A).Opens))) :
        eRestr.inv (r • m) = eR r • eRestr.inv m := by
      change (M.restrictAppIso f ⊤).inv (r • m) =
        (f.appIso ⊤).hom r • (M.restrictAppIso f ⊤).inv m
      simp
    letI : RingHomInvPair
        (eR : Γ(X, f ''ᵁ (⊤ : (Spec A).Opens)) →+* Γ(Spec A, ⊤))
        (eR.symm : Γ(Spec A, ⊤) →+*
          Γ(X, f ''ᵁ (⊤ : (Spec A).Opens))) :=
      RingHomInvPair.of_ringEquiv eR
    letI : RingHomInvPair
        (eR.symm : Γ(Spec A, ⊤) →+*
          Γ(X, f ''ᵁ (⊤ : (Spec A).Opens)))
        (eR : Γ(X, f ''ᵁ (⊤ : (Spec A).Opens)) →+* Γ(Spec A, ⊤)) :=
      RingHomInvPair.of_ringEquiv eR.symm
    let eM : Γ(M, f ''ᵁ (⊤ : (Spec A).Opens))
        ≃ₛₗ[(eR : Γ(X, f ''ᵁ (⊤ : (Spec A).Opens)) →+* Γ(Spec A, ⊤))]
          Γ(N, ⊤) :=
      { toEquiv :=
          { toFun := fun m ↦ ePull (eRestr.inv m)
            invFun := fun n ↦ eRestr.hom (ePull.symm n)
            left_inv := fun m ↦ by simp
            right_inv := fun n ↦ by simp }
        map_add' := fun a b ↦ by simp
        map_smul' := fun r m ↦ by
          change ePull (eRestr.inv (r • m)) = eR r • ePull (eRestr.inv m)
          rw [hres r m]
          exact ePull.map_smul (eR r) (eRestr.inv m) }
    letI : Module.FinitePresentation
        Γ(X, f ''ᵁ (⊤ : (Spec A).Opens))
        Γ(M, f ''ᵁ (⊤ : (Spec A).Opens)) := hImage
    have hNtop : Module.FinitePresentation Γ(Spec A, ⊤) Γ(N, ⊤) :=
      Module.FinitePresentation.of_semilinearEquiv eR eM
    have hNmod : Module.FinitePresentation A (moduleSpecΓFunctor.obj N) :=
      moduleSpecΓFunctor_finitePresentation_of_top N hNtop
    letI : Module.FinitePresentation A (moduleSpecΓFunctor.obj N) := hNmod
    have hN : N.IsFinitePresentation :=
      isFinitePresentation_of_moduleSpecΓFunctor N
    letI : N.IsFinitePresentation := hN
    have hBack : ((Scheme.Modules.pullback X.isoSpec.hom).obj N).IsFinitePresentation := by
      infer_instance
    let eBack : (Scheme.Modules.pullback X.isoSpec.hom).obj N ≅ M :=
      (Scheme.Modules.pullbackComp X.isoSpec.hom X.isoSpec.inv).app M ≪≫
        (Scheme.Modules.pullbackCongr X.isoSpec.hom_inv_id).app M ≪≫
        (Scheme.Modules.pullbackId _).app M
    exact ObjectProperty.prop_of_iso
      (P := SheafOfModules.isFinitePresentation X.ringCatSheaf) eBack hBack

/-- Finite presentation of a quasicoherent sheaf is detected on its modules of
sections over all affine opens. -/
lemma Scheme.Modules.isFinitePresentation_iff_sections_affineOpens
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] :
    M.IsFinitePresentation ↔
      ∀ U : X.affineOpens,
        Module.FinitePresentation Γ(X, U.1) Γ(M, U.1) := by
  constructor
  · intro hM U
    letI : M.IsFinitePresentation := hM
    have hPull : ((Scheme.Modules.pullback U.1.ι).obj M).IsFinitePresentation := by
      infer_instance
    have hMU : (M.restrict U.1.ι).IsFinitePresentation :=
      ObjectProperty.prop_of_iso
        (P := SheafOfModules.isFinitePresentation U.1.toScheme.ringCatSheaf)
        ((Scheme.Modules.restrictFunctorIsoPullback U.1.ι).app M).symm hPull
    letI : (M.restrict U.1.ι).IsFinitePresentation := hMU
    obtain ⟨P, hP⟩ :=
      Scheme.Modules.exists_finitePresentation_of_isFinitePresentation_affine
        (M.restrict U.1.ι)
    letI : P.IsFinite := hP
    exact Scheme.Modules.finitePresentation_sections_of_restrict_presentation M U P
  · intro hM
    let presData (U : X.affineOpens) :
        { P : SheafOfModules.Presentation (M.restrict U.1.ι) // P.IsFinite } := by
      have him : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) = U.1 := by
        rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
      have hImage : Module.FinitePresentation
          Γ(X, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))
          Γ(M, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) :=
        Scheme.Modules.sections_finitePresentation_of_eq M U.1 _ him.symm (hM U)
      let eR := (U.1.ι.appIso ⊤).commRingCatIsoToRingEquiv
      letI : RingHomInvPair
          (eR : Γ(X, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) →+*
            Γ(U.1.toScheme, ⊤))
          (eR.symm : Γ(U.1.toScheme, ⊤) →+*
            Γ(X, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))) :=
        RingHomInvPair.of_ringEquiv eR
      letI : RingHomInvPair
          (eR.symm : Γ(U.1.toScheme, ⊤) →+*
            Γ(X, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)))
          (eR : Γ(X, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) →+*
            Γ(U.1.toScheme, ⊤)) :=
        RingHomInvPair.of_ringEquiv eR.symm
      let eM : Γ(M, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))
          ≃ₛₗ[(eR : Γ(X, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) →+*
            Γ(U.1.toScheme, ⊤))]
            Γ(M.restrict U.1.ι, ⊤) :=
        { toEquiv :=
            { toFun := (M.restrictAppIso U.1.ι ⊤).inv
              invFun := (M.restrictAppIso U.1.ι ⊤).hom
              left_inv := fun m ↦ by simp
              right_inv := fun m ↦ by simp }
          map_add' := fun a b ↦ by simp
          map_smul' := fun r m ↦ by
            change (M.restrictAppIso U.1.ι ⊤).inv (r • m) =
              (U.1.ι.appIso ⊤).hom r • (M.restrictAppIso U.1.ι ⊤).inv m
            simp }
      letI : Module.FinitePresentation
          Γ(X, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens))
          Γ(M, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) := hImage
      have htop : Module.FinitePresentation Γ(U.1.toScheme, ⊤)
          Γ(M.restrict U.1.ι, ⊤) :=
        Module.FinitePresentation.of_semilinearEquiv eR eM
      have hRestrict : (M.restrict U.1.ι).IsFinitePresentation :=
        (Scheme.Modules.isFinitePresentation_iff_sections_top
          (M.restrict U.1.ι)).mpr htop
      letI : (M.restrict U.1.ι).IsFinitePresentation := hRestrict
      let h :=
        Scheme.Modules.exists_finitePresentation_of_isFinitePresentation_affine
          (M.restrict U.1.ι)
      exact ⟨Classical.choose h, Classical.choose_spec h⟩
    let pres (U : X.affineOpens) :
        SheafOfModules.Presentation (M.restrict U.1.ι) := (presData U).1
    letI (U : X.affineOpens) : (pres U).IsFinite := (presData U).2
    exact Scheme.Modules.isFinitePresentation_of_isOpenCover M
      (fun U : X.affineOpens ↦ U.1) (iSup_affineOpens_eq_top X) pres

/-- The structure sheaf, viewed as a module over itself, is finitely presented. -/
lemma Scheme.Modules.unit_isFinitePresentation (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation := by
  letI : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
    Scheme.Modules.unit_isQuasicoherent X
  rw [Scheme.Modules.isFinitePresentation_iff_sections_affineOpens]
  intro U
  change Module.FinitePresentation Γ(X, U.1) Γ(X, U.1)
  infer_instance

namespace Scheme

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- A quasicoherent quotient of the structure sheaf whose kernel is the ideal of a
closed immersion is isomorphic, compatibly with the quotient maps, to the quotient
attached to that closed immersion. -/
lemma Modules.Hom.exists_iso_closedQuotient_of_kernelIdealSheafData_eq
    (Q : X.Modules) [Q.IsQuasicoherent]
    (φ : SheafOfModules.unit X.ringCatSheaf ⟶ Q) [Epi φ]
    (hφ : Modules.Hom.kernelIdealSheafData Q φ = i.ker) :
    ∃ e : Q ≅ i.closedQuotient, φ ≫ e.hom = i.toClosedQuotient := by
  apply Modules.Hom.exists_iso_of_kernelIdealSheafData_eq
  rw [hφ, i.kernelIdealSheafData_toClosedQuotient]

/-- On an open of the ambient scheme, sections of the quotient associated to a
closed immersion are the sections of the structure sheaf on the inverse-image open.
The equivalence records the scalar action through the closed immersion. -/
noncomputable def Hom.closedQuotientSectionsLinearEquiv (U : X.Opens) :
    letI := Module.compHom Γ(Z, i ⁻¹ᵁ U) (i.app U).hom
    Γ(i.closedQuotient, U) ≃ₗ[Γ(X, U)] Γ(Z, i ⁻¹ᵁ U) :=
  by
    letI : Module Γ(X, U) Γ(Z, i ⁻¹ᵁ U) :=
      Module.compHom Γ(Z, i ⁻¹ᵁ U) (i.app U).hom
    exact
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ by
          change r • x = (RingHom.id _) r • x
          rw [RingHom.id_apply] }

/-- The section equivalence for a closed quotient, with scalars restricted from a
base scheme through a chosen ambient structure morphism. -/
noncomputable def Hom.closedQuotientSectionsLinearEquivOver (p : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (hUV : U ≤ p ⁻¹ᵁ V) :
    let a := (X.presheaf.map (homOfLE hUV).op).hom.comp (p.app V).hom
    let b := (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom.comp
      (p.appLE V U hUV).hom
    letI := Module.compHom Γ(i.closedQuotient, U) a
    letI := Module.compHom Γ(Z, i ⁻¹ᵁ U) b
    Γ(i.closedQuotient, U) ≃ₗ[Γ(S, V)] Γ(Z, i ⁻¹ᵁ U) :=
  by
    let a := (X.presheaf.map (homOfLE hUV).op).hom.comp (p.app V).hom
    let b := (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom.comp
      (p.appLE V U hUV).hom
    have hab : (i.app U).hom.comp a = b := by
      ext r
      dsimp [a, b, Scheme.Hom.appLE]
      simp
    letI : Module Γ(S, V) Γ(i.closedQuotient, U) :=
      Module.compHom Γ(i.closedQuotient, U) a
    letI : Module Γ(S, V) Γ(Z, i ⁻¹ᵁ U) :=
      Module.compHom Γ(Z, i ⁻¹ᵁ U) b
    exact
      { toFun := fun x ↦ x
        invFun := fun x ↦ x
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun r x ↦ by
          change (i.app U).hom (a r) * (show Γ(Z, i ⁻¹ᵁ U) from x) =
            b r * (show Γ(Z, i ⁻¹ᵁ U) from x)
          exact congrArg
            (fun c : Γ(Z, i ⁻¹ᵁ U) ↦ c * (show Γ(Z, i ⁻¹ᵁ U) from x))
            (RingHom.congr_fun hab r) }

/-- For an affine morphism, local finite presentation is detected by its coordinate
map over each affine open of the target. -/
lemma Hom.locallyOfFinitePresentation_iff_app_of_isAffineHom
    {Y W : Scheme.{u}} (f : Y ⟶ W) [IsAffineHom f] :
    LocallyOfFinitePresentation f ↔
      ∀ U : W.affineOpens, (f.app U.1).hom.FinitePresentation := by
  constructor
  · intro hf U
    letI : LocallyOfFinitePresentation f := hf
    rw [f.app_eq_appLE]
    exact f.finitePresentation_appLE U.2
      ((inferInstance : IsAffineHom f).isAffine_preimage U.1 U.2) le_rfl
  · intro hf
    have ht : targetAffineLocally (affineAnd @RingHom.FinitePresentation) f :=
      (targetAffineLocally_affineAnd_iff'
        RingHom.finitePresentation_respectsIso f).mpr
        ⟨inferInstance, fun U hU ↦ hf ⟨U, hU⟩⟩
    have ha : affineLocally @RingHom.FinitePresentation f :=
      ((targetAffineLocally_affineAnd_iff_affineLocally
        RingHom.finitePresentation_isLocal f).mp ht).2
    rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation]
    exact ha

/-- If a composite is locally of finite presentation and the second morphism is
locally of finite type, then the first morphism is locally of finite presentation. -/
lemma locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType
    {Y W B : Scheme.{u}} (f : Y ⟶ W) (g : W ⟶ B)
    (hfg : LocallyOfFinitePresentation (f ≫ g))
    (hg : LocallyOfFiniteType g) : LocallyOfFinitePresentation f := by
  wlog hB : IsAffine B generalizing Y W B
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top
      (P := @LocallyOfFinitePresentation) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top B))]
    intro U
    have hfg' := IsZariskiLocalAtTarget.restrict hfg U.1
    rw [morphismRestrict_comp] at hfg'
    exact this _ _ hfg' (IsZariskiLocalAtTarget.restrict hg U.1) U.2
  letI : LocallyOfFinitePresentation (f ≫ g) := hfg
  letI : LocallyOfFiniteType g := hg
  rw [HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation)]
  intro U V e
  have hcomp := (f ≫ g).finitePresentation_appLE
    (isAffineOpen_top B) V.2 le_top
  have hgU := g.finiteType_appLE (isAffineOpen_top B) U.2 le_top
  have heq :
      (f.appLE U.1 V.1 e).hom.comp (g.appLE ⊤ U.1 le_top).hom =
        ((f ≫ g).appLE ⊤ V.1 le_top).hom := by
    rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  exact (heq.symm ▸ hcomp).of_comp_finiteType
    (g.appLE ⊤ U.1 le_top).hom hgU

/-- A closed immersion is locally of finite presentation exactly when its associated
quotient of the ambient structure sheaf is finitely presented. -/
lemma Hom.closedQuotient_isFinitePresentation_iff :
    i.closedQuotient.IsFinitePresentation ↔ LocallyOfFinitePresentation i := by
  rw [Modules.isFinitePresentation_iff_sections_affineOpens,
    i.locallyOfFinitePresentation_iff_app_of_isAffineHom]
  constructor
  · intro hM U
    letI : Module.FinitePresentation Γ(X, U.1) Γ(i.closedQuotient, U.1) := hM U
    have hZ :
        letI := Module.compHom Γ(Z, i ⁻¹ᵁ U.1) (i.app U.1).hom
        Module.FinitePresentation Γ(X, U.1) Γ(Z, i ⁻¹ᵁ U.1) := by
      letI : Module Γ(X, U.1) Γ(Z, i ⁻¹ᵁ U.1) :=
        Module.compHom Γ(Z, i ⁻¹ᵁ U.1) (i.app U.1).hom
      exact Module.FinitePresentation.of_equiv
        (i.closedQuotientSectionsLinearEquiv U.1)
    exact (RingHom.FinitePresentation.iff_module_of_surjective
      (i.app U.1).hom (i.app_surjective U.1 U.2)).mpr hZ
  · intro hi U
    have hZ :
        letI := Module.compHom Γ(Z, i ⁻¹ᵁ U.1) (i.app U.1).hom
        Module.FinitePresentation Γ(X, U.1) Γ(Z, i ⁻¹ᵁ U.1) :=
      (RingHom.FinitePresentation.iff_module_of_surjective
        (i.app U.1).hom (i.app_surjective U.1 U.2)).mp (hi U)
    letI : Module Γ(X, U.1) Γ(Z, i ⁻¹ᵁ U.1) :=
      Module.compHom Γ(Z, i ⁻¹ᵁ U.1) (i.app U.1).hom
    letI : Module.FinitePresentation Γ(X, U.1) Γ(Z, i ⁻¹ᵁ U.1) := hZ
    exact Module.FinitePresentation.of_equiv
      (i.closedQuotientSectionsLinearEquiv U.1).symm

/-- Relative flatness of the closed quotient supplies flatness of the affine
coordinate map on every inverse image of an ambient affine open. -/
lemma Hom.appLE_flat_of_closedQuotient_flatOver (p : X ⟶ S)
    (hM : i.closedQuotient.FlatOver p)
    (U : X.affineOpens) (V : S.affineOpens)
    (hUV : U.1 ≤ p ⁻¹ᵁ V.1)
    (hZU : i ⁻¹ᵁ U.1 ≤ (i ≫ p) ⁻¹ᵁ V.1) :
    ((i ≫ p).appLE V.1 (i ⁻¹ᵁ U.1) hZU).hom.Flat := by
  let a : Γ(S, V.1) →+* Γ(X, U.1) :=
    (X.presheaf.map (homOfLE hUV).op).hom.comp (p.app V.1).hom
  let b : Γ(S, V.1) →+* Γ(Z, i ⁻¹ᵁ U.1) :=
    (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom.comp
      (p.appLE V.1 U.1 hUV).hom
  have hQ :
      letI := Module.compHom Γ(i.closedQuotient, U.1) a
      Module.Flat Γ(S, V.1) Γ(i.closedQuotient, U.1) :=
    hM U V hUV
  letI : Module Γ(S, V.1) Γ(i.closedQuotient, U.1) :=
    Module.compHom Γ(i.closedQuotient, U.1) a
  letI : Module.Flat Γ(S, V.1) Γ(i.closedQuotient, U.1) := hQ
  letI : Module Γ(S, V.1) Γ(Z, i ⁻¹ᵁ U.1) :=
    Module.compHom Γ(Z, i ⁻¹ᵁ U.1) b
  have hb : Module.Flat Γ(S, V.1) Γ(Z, i ⁻¹ᵁ U.1) :=
    Module.Flat.of_linearEquiv
      (i.closedQuotientSectionsLinearEquivOver p U.1 V.1 hUV).symm
  have hb' : b.Flat := hb
  have hab : b = ((i ≫ p).appLE V.1 (i ⁻¹ᵁ U.1) hZU).hom := by
    dsimp only [b]
    rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  exact hab ▸ hb'

/-- If the closed subscheme is flat over a base, its associated quotient of the
ambient structure sheaf is flat over that base. -/
lemma Hom.closedQuotient_flatOver_of_flat (p : X ⟶ S)
    (h : Flat (i ≫ p)) : i.closedQuotient.FlatOver p := by
  letI : Flat (i ≫ p) := h
  intro U V hUV
  have hpre : IsAffineOpen (i ⁻¹ᵁ U.1) := U.2.preimage i
  have hZU : i ⁻¹ᵁ U.1 ≤ (i ≫ p) ⁻¹ᵁ V.1 := by
    change i ⁻¹ᵁ U.1 ≤ i ⁻¹ᵁ (p ⁻¹ᵁ V.1)
    exact i.preimage_mono hUV
  have hflat := (i ≫ p).flat_appLE V.2 hpre hZU
  let a : Γ(S, V.1) →+* Γ(Z, i ⁻¹ᵁ U.1) :=
    ((i ≫ p).appLE V.1 (i ⁻¹ᵁ U.1) hZU).hom
  let b : Γ(S, V.1) →+* Γ(Z, i ⁻¹ᵁ U.1) :=
    (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom.comp
      (p.appLE V.1 U.1 hUV).hom
  have hab : a = b := by
    dsimp only [a, b]
    rw [← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  have hflat' :
      letI := Module.compHom Γ(Z, i ⁻¹ᵁ U.1) a
      Module.Flat Γ(S, V.1) Γ(Z, i ⁻¹ᵁ U.1) := hflat
  have hb := Module.Flat.compHom_congr a b hab hflat'
  letI : Module Γ(S, V.1) Γ(Z, i ⁻¹ᵁ U.1) :=
    Module.compHom Γ(Z, i ⁻¹ᵁ U.1) b
  letI : Module.Flat Γ(S, V.1) Γ(Z, i ⁻¹ᵁ U.1) := hb
  letI : Module Γ(S, V.1) Γ(i.closedQuotient, U.1) :=
    Module.compHom Γ(i.closedQuotient, U.1)
      ((X.presheaf.map (homOfLE hUV).op).hom.comp (p.app V.1).hom)
  exact Module.Flat.of_linearEquiv
    (i.closedQuotientSectionsLinearEquivOver p U.1 V.1 hUV)

/-- If the quotient of the ambient structure sheaf associated to a closed immersion
is flat over the base, then the closed subscheme itself is flat over the base. -/
lemma Hom.flat_of_closedQuotient_flatOver (p : X ⟶ S)
    (hM : i.closedQuotient.FlatOver p) : Flat (i ≫ p) := by
  classical
  let g : Z ⟶ S := i ≫ p
  let k (z : Z) := S.affineCover.idx (g z)
  let V (z : Z) : S.affineOpens :=
    ⟨(S.affineCover.f (k z)).opensRange,
      isAffineOpen_opensRange (S.affineCover.f (k z))⟩
  have hzV (z : Z) : g z ∈ (V z).1 := S.affineCover.covers (g z)
  have hex (z : Z) :
      ∃ U : X.affineOpens, i z ∈ U.1 ∧ U.1 ≤ p ⁻¹ᵁ (V z).1 := by
    have hiz : i z ∈ p ⁻¹ᵁ (V z).1 := by
      change p (i z) ∈ (V z).1
      exact hzV z
    obtain ⟨_, ⟨U, hU, rfl⟩, hizU, hUV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        hiz (p ⁻¹ᵁ (V z).1).2
    exact ⟨⟨U, hU⟩, hizU, hUV⟩
  choose U hizU hUV using hex
  let W (z : Z) : Z.Opens := i ⁻¹ᵁ (U z).1
  have hWtop : ⨆ z, W z = ⊤ := by
    apply top_unique
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨z, hizU z⟩
  apply IsZariskiLocalAtSource.of_iSup_eq_top W hWtop
  intro z
  have hWVS : W z ≤ g ⁻¹ᵁ (V z).1 := by
    change i ⁻¹ᵁ (U z).1 ≤ i ⁻¹ᵁ (p ⁻¹ᵁ (V z).1)
    exact i.preimage_mono (hUV z)
  let q : (W z).toScheme ⟶ (V z).1.toScheme :=
    g.resLE (V z).1 (W z) hWVS
  have hqAppLE :
      (g.appLE (V z).1 (W z) hWVS).hom.Flat := by
    exact i.appLE_flat_of_closedQuotient_flatOver p hM (U z) (V z)
      (hUV z) hWVS
  haveI : IsAffine (W z).toScheme := (U z).2.preimage i
  haveI : IsAffine (V z).1.toScheme := (V z).2
  have hqAppTop : q.appTop.hom.Flat :=
    (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso g (V z).1 (W z) hWVS)).mpr hqAppLE
  have hq : Flat q :=
    (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mpr hqAppTop
  letI : Flat q := hq
  have hcomp : Flat (q ≫ (V z).1.ι) := inferInstance
  simpa only [q, g, Scheme.Hom.resLE_comp_ι] using hcomp

/-- A closed subscheme is flat over a base exactly when its associated quotient of
the ambient structure sheaf is flat over that base. -/
lemma Hom.closedQuotient_flatOver_iff (p : X ⟶ S) :
    i.closedQuotient.FlatOver p ↔ Flat (i ≫ p) :=
  ⟨i.flat_of_closedQuotient_flatOver p, i.closedQuotient_flatOver_of_flat p⟩

namespace Modules.QuotientPullbackData

variable {X S : Scheme.{u}} {f : X ⟶ S} {T T' : Over S}

/-- Normalize a quotient of the pulled-back structure sheaf to a morphism from the
structure sheaf of the base-changed ambient scheme. -/
noncomputable def normalizedUnitMap
    (x : QuotientPullbackData (SheafOfModules.unit X.ringCatSheaf) f T) :
    SheafOfModules.unit ((Over.pullback f).obj T).left.ringCatSheaf ⟶ x.Q :=
  inv (SheafOfModules.pullbackObjUnitToUnit
    ((Over.pullback f).obj T).hom.toRingCatSheafHom) ≫ x.π

instance normalizedUnitMap_epi
    (x : QuotientPullbackData (SheafOfModules.unit X.ringCatSheaf) f T) :
    Epi x.normalizedUnitMap := by
  haveI : Epi x.π := x.epi
  dsimp only [normalizedUnitMap]
  infer_instance

/-- Normalizing a quotient after base change agrees with the normalized pullback
of its quotient map. -/
lemma normalizedUnitMap_pullback (g : T' ⟶ T)
    (x : QuotientPullbackData (SheafOfModules.unit X.ringCatSheaf) f T) :
    (x.pullback g).normalizedUnitMap =
      Modules.Hom.pullbackUnitMap ((Over.pullback f).map g).left
        x.normalizedUnitMap := by
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit
      ((Over.pullback f).obj T').hom.toRingCatSheafHom) := inferInstance
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit
      ((Over.pullback f).map g).left.toRingCatSheafHom) := inferInstance
  let _ : IsIso (SheafOfModules.pullbackObjUnitToUnit
      ((Over.pullback f).obj T).hom.toRingCatSheafHom) := inferInstance
  let e := PullbackQuotient.pullbackComparison
    (SheafOfModules.unit X.ringCatSheaf) ((Over.pullback f).map g)
  have he :
      inv (SheafOfModules.pullbackObjUnitToUnit
          ((Over.pullback f).obj T').hom.toRingCatSheafHom) ≫ e.hom =
        inv (SheafOfModules.pullbackObjUnitToUnit
            ((Over.pullback f).map g).left.toRingCatSheafHom) ≫
          (Modules.pullback ((Over.pullback f).map g).left).map
            (inv (SheafOfModules.pullbackObjUnitToUnit
              ((Over.pullback f).obj T).hom.toRingCatSheafHom)) := by
    rw [← cancel_mono e.inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    dsimp only [e, PullbackQuotient.pullbackComparison, Iso.trans_inv,
      Iso.symm_inv]
    calc
      inv (SheafOfModules.pullbackObjUnitToUnit
          ((Over.pullback f).obj T').hom.toRingCatSheafHom) =
        inv (SheafOfModules.pullbackObjUnitToUnit
            (((Over.pullback f).map g).left ≫
              ((Over.pullback f).obj T).hom).toRingCatSheafHom) ≫
          (Modules.pullbackCongr
            (Over.w ((Over.pullback f).map g))).hom.app
              (SheafOfModules.unit X.ringCatSheaf) :=
        (Modules.pullbackObjUnitToUnit_inv_comp_pullbackCongr
          (Over.w ((Over.pullback f).map g))).symm
      _ = ((inv (SheafOfModules.pullbackObjUnitToUnit
              ((Over.pullback f).map g).left.toRingCatSheafHom) ≫
            (Modules.pullback ((Over.pullback f).map g).left).map
              (inv (SheafOfModules.pullbackObjUnitToUnit
                ((Over.pullback f).obj T).hom.toRingCatSheafHom))) ≫
            (Modules.pullbackComp ((Over.pullback f).map g).left
              ((Over.pullback f).obj T).hom).hom.app
                (SheafOfModules.unit X.ringCatSheaf)) ≫
          (Modules.pullbackCongr
            (Over.w ((Over.pullback f).map g))).hom.app
              (SheafOfModules.unit X.ringCatSheaf) := by
        exact congrArg
          (fun k ↦ k ≫
            (Modules.pullbackCongr
              (Over.w ((Over.pullback f).map g))).hom.app
                (SheafOfModules.unit X.ringCatSheaf))
          (Modules.pullbackObjUnitToUnit_inv_comp_pullbackComp
            ((Over.pullback f).map g).left
              ((Over.pullback f).obj T).hom).symm
      _ = _ := by rfl
  dsimp only [normalizedUnitMap, QuotientPullbackData.pullback,
    PullbackQuotient.pullbackComparison, Modules.Hom.pullbackUnitMap,
    Iso.trans_hom, Iso.symm_hom]
  rw [Functor.map_comp]
  dsimp only [e, PullbackQuotient.pullbackComparison, Iso.trans_hom,
    Iso.symm_hom] at he
  rw [← Category.assoc]
  rw [he]
  rw [Category.assoc]

/-- The ideal sheaf cut out by a quotient of the pulled-back structure sheaf. -/
noncomputable def idealSheafData
    (x : QuotientPullbackData (SheafOfModules.unit X.ringCatSheaf) f T) :
    ((Over.pullback f).obj T).left.IdealSheafData := by
  letI : x.Q.IsQuasicoherent := x.isQuasicoherent
  exact Modules.Hom.kernelIdealSheafData x.Q x.normalizedUnitMap

/-- The ideal sheaf cut out by a quotient commutes with pullback of the quotient
family. -/
lemma idealSheafData_pullback (g : T' ⟶ T)
    (x : QuotientPullbackData (SheafOfModules.unit X.ringCatSheaf) f T) :
    (x.pullback g).idealSheafData =
      x.idealSheafData.comap ((Over.pullback f).map g).left := by
  haveI : x.Q.IsQuasicoherent := x.isQuasicoherent
  haveI : ((Modules.pullback ((Over.pullback f).map g).left).obj
      x.Q).IsQuasicoherent := inferInstance
  change Modules.Hom.kernelIdealSheafData
      ((Modules.pullback ((Over.pullback f).map g).left).obj x.Q)
        (x.pullback g).normalizedUnitMap =
    (Modules.Hom.kernelIdealSheafData x.Q x.normalizedUnitMap).comap
      ((Over.pullback f).map g).left
  rw [normalizedUnitMap_pullback]
  exact Modules.Hom.kernelIdealSheafData_pullback_of_epi
    ((Over.pullback f).map g).left x.Q x.normalizedUnitMap

/-- Equivalent quotient presentations of the pulled-back structure sheaf determine
the same kernel ideal sheaf. -/
lemma idealSheafData_eq_of_r
    {x y : QuotientPullbackData (SheafOfModules.unit X.ringCatSheaf) f T}
    (h : (QuotientPullbackData.setoid
      (SheafOfModules.unit X.ringCatSheaf) f T).r x y) :
    x.idealSheafData = y.idealSheafData := by
  haveI : x.Q.IsQuasicoherent := x.isQuasicoherent
  haveI : y.Q.IsQuasicoherent := y.isQuasicoherent
  obtain ⟨e, he⟩ := h
  change Modules.Hom.kernelIdealSheafData x.Q x.normalizedUnitMap =
    Modules.Hom.kernelIdealSheafData y.Q y.normalizedUnitMap
  apply Modules.Hom.kernelIdealSheafData_eq_of_iso x.Q y.Q
    x.normalizedUnitMap y.normalizedUnitMap e
  dsimp only [normalizedUnitMap]
  rw [Category.assoc, he]

/-- Quotient presentations of the pulled-back structure sheaf are equivalent as
soon as they determine the same kernel ideal sheaf. -/
lemma r_of_idealSheafData_eq
    (x y : QuotientPullbackData (SheafOfModules.unit X.ringCatSheaf) f T)
    (h : x.idealSheafData = y.idealSheafData) :
    (QuotientPullbackData.setoid
      (SheafOfModules.unit X.ringCatSheaf) f T).r x y := by
  haveI : x.Q.IsQuasicoherent := x.isQuasicoherent
  haveI : y.Q.IsQuasicoherent := y.isQuasicoherent
  change Modules.Hom.kernelIdealSheafData x.Q x.normalizedUnitMap =
    Modules.Hom.kernelIdealSheafData y.Q y.normalizedUnitMap at h
  obtain ⟨e, he⟩ := Modules.Hom.exists_iso_of_kernelIdealSheafData_eq
    x.Q y.Q x.normalizedUnitMap y.normalizedUnitMap h
  refine ⟨e, ?_⟩
  apply (cancel_epi (inv (SheafOfModules.pullbackObjUnitToUnit
    ((Over.pullback f).obj T).hom.toRingCatSheafHom))).mp
  simpa only [normalizedUnitMap, Category.assoc] using he

/-- Two quotient presentations of the pulled-back structure sheaf are equivalent
exactly when they determine the same kernel ideal sheaf. -/
lemma r_iff_idealSheafData_eq
    (x y : QuotientPullbackData (SheafOfModules.unit X.ringCatSheaf) f T) :
    (QuotientPullbackData.setoid
      (SheafOfModules.unit X.ringCatSheaf) f T).r x y ↔
      x.idealSheafData = y.idealSheafData :=
  ⟨idealSheafData_eq_of_r, r_of_idealSheafData_eq x y⟩

/-- The kernel ideal of a flat finitely presented quotient of the pulled-back
structure sheaf defines a flat finitely presented closed family. -/
lemma idealSheafData_isFlatFamilyOver
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (x : QuotientPullbackData (SheafOfModules.unit X.ringCatSheaf) f T) :
    x.idealSheafData.IsFlatFamilyOver f T := by
  let p := pullback.fst T.hom f
  let j := x.idealSheafData.subschemeι
  haveI : x.Q.IsQuasicoherent := x.isQuasicoherent
  have hker : Modules.Hom.kernelIdealSheafData x.Q x.normalizedUnitMap = j.ker := by
    rw [IdealSheafData.ker_subschemeι]
    rfl
  obtain ⟨e, _⟩ :=
    Modules.Hom.exists_iso_closedQuotient_of_kernelIdealSheafData_eq
      j x.Q x.normalizedUnitMap hker
  have hflatQ : x.Q.FlatOver p := x.flatOver
  have hflatClosed : j.closedQuotient.FlatOver p :=
    Modules.FlatOver.of_iso e hflatQ
  have hflat : Flat (j ≫ p) := j.flat_of_closedQuotient_flatOver p hflatClosed
  have hfpClosed : j.closedQuotient.IsFinitePresentation :=
    ObjectProperty.prop_of_iso
      (P := SheafOfModules.isFinitePresentation
        ((Over.pullback f).obj T).left.ringCatSheaf)
      e x.isFinitePresentation
  have hjfp : LocallyOfFinitePresentation j :=
    j.closedQuotient_isFinitePresentation_iff.mp hfpClosed
  have hpFP : LocallyOfFinitePresentation p := by
    dsimp only [p]
    infer_instance
  letI : LocallyOfFinitePresentation j := hjfp
  letI : LocallyOfFinitePresentation p := hpFP
  have hlfp : LocallyOfFinitePresentation (j ≫ p) := inferInstance
  have hpqc : QuasiCompact p := by
    dsimp only [p]
    infer_instance
  have hpqs : QuasiSeparated p := by
    dsimp only [p]
    infer_instance
  letI : QuasiCompact p := hpqc
  letI : QuasiSeparated p := hpqs
  have hqc : QuasiCompact (j ≫ p) := inferInstance
  have hqs : QuasiSeparated (j ≫ p) := inferInstance
  exact ⟨hflat, hlfp, hqc, hqs⟩

end Modules.QuotientPullbackData

namespace IdealSheafData

variable {X S : Scheme.{u}} {f : X ⟶ S} {T : Over S}

/-- A flat finitely presented closed family determines the corresponding quotient
of the pulled-back ambient structure sheaf. -/
noncomputable def toStructureSheafQuotientData [LocallyOfFinitePresentation f]
    (I : ((Over.pullback f).obj T).left.IdealSheafData)
    (hI : I.IsFlatFamilyOver f T) :
    Modules.QuotientPullbackData (SheafOfModules.unit X.ringCatSheaf) f T where
  Q := I.subschemeι.closedQuotient
  isQuasicoherent := inferInstance
  isFinitePresentation := by
    have hp : LocallyOfFinitePresentation (pullback.fst T.hom f) := by
      infer_instance
    letI : LocallyOfFinitePresentation (pullback.fst T.hom f) := hp
    have hpft : LocallyOfFiniteType (pullback.fst T.hom f) := by infer_instance
    exact I.subschemeι.closedQuotient_isFinitePresentation_iff.mpr
      (locallyOfFinitePresentation_of_comp_of_locallyOfFiniteType
        I.subschemeι (pullback.fst T.hom f) hI.2.1 hpft)
  flatOver := I.subschemeι.closedQuotient_flatOver_of_flat
    (pullback.fst T.hom f) hI.1
  π := SheafOfModules.pullbackObjUnitToUnit
      ((Over.pullback f).obj T).hom.toRingCatSheafHom ≫
    I.subschemeι.toClosedQuotient
  epi := by
    letI : Epi (SheafOfModules.pullbackObjUnitToUnit
        ((Over.pullback f).obj T).hom.toRingCatSheafHom) := inferInstance
    letI : Epi I.subschemeι.toClosedQuotient := inferInstance
    infer_instance

/-- Recovering the kernel ideal from the quotient attached to a closed family gives
the original ideal sheaf. -/
lemma idealSheafData_toStructureSheafQuotientData
    [LocallyOfFinitePresentation f]
    (I : ((Over.pullback f).obj T).left.IdealSheafData)
    (hI : I.IsFlatFamilyOver f T) :
    (I.toStructureSheafQuotientData hI).idealSheafData = I := by
  change Modules.Hom.kernelIdealSheafData I.subschemeι.closedQuotient
      (inv (SheafOfModules.pullbackObjUnitToUnit
          ((Over.pullback f).obj T).hom.toRingCatSheafHom) ≫
        (SheafOfModules.pullbackObjUnitToUnit
            ((Over.pullback f).obj T).hom.toRingCatSheafHom ≫
          I.subschemeι.toClosedQuotient)) = I
  rw [IsIso.inv_hom_id_assoc,
    I.subschemeι.kernelIdealSheafData_toClosedQuotient,
    I.ker_subschemeι]

end IdealSheafData

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Send a Hilbert-family point to the isomorphism class of its quotient structure
sheaf. -/
noncomputable def hilbertToStructureSheafQuotientAt
    [LocallyOfFinitePresentation f] (T : Over S) :
    (hilbFunctor f).obj (op T) →
      (quotFunctor (SheafOfModules.unit X.ringCatSheaf) f).obj (op T) :=
  fun I ↦ ⟦I.1.toStructureSheafQuotientData I.2⟧

/-- Recover the Hilbert-family point cut out by the kernel of a quotient of the
pulled-back structure sheaf. -/
noncomputable def structureSheafQuotientToHilbertAt
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (T : Over S) :
    (quotFunctor (SheafOfModules.unit X.ringCatSheaf) f).obj (op T) →
      (hilbFunctor f).obj (op T) :=
  Quotient.lift
    (fun x ↦ ⟨x.idealSheafData, x.idealSheafData_isFlatFamilyOver⟩)
    (fun _ _ h ↦ Subtype.ext
      (Modules.QuotientPullbackData.idealSheafData_eq_of_r h))

/-- For a locally finitely presented, quasi-compact, and quasi-separated ambient
morphism, Hilbert families are equivalent pointwise to quotients of the structure
sheaf. -/
noncomputable def hilbertStructureSheafQuotientEquiv
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (T : Over S) :
    (hilbFunctor f).obj (op T) ≃
      (quotFunctor (SheafOfModules.unit X.ringCatSheaf) f).obj (op T) where
  toFun := hilbertToStructureSheafQuotientAt f T
  invFun := structureSheafQuotientToHilbertAt f T
  left_inv I := by
    apply Subtype.ext
    exact I.1.idealSheafData_toStructureSheafQuotientData I.2
  right_inv q := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    apply Quotient.sound
    apply Modules.QuotientPullbackData.r_of_idealSheafData_eq
    exact x.idealSheafData.idealSheafData_toStructureSheafQuotientData
      x.idealSheafData_isFlatFamilyOver

/-- The map from Hilbert families to quotients of the structure sheaf commutes
with arbitrary base change. -/
lemma hilbertToStructureSheafQuotientAt_naturality
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    {T T' : Over S} (g : T' ⟶ T)
    (I : (hilbFunctor f).obj (op T)) :
    hilbertToStructureSheafQuotientAt f T'
        ((hilbFunctor f).map g.op I) =
      (quotFunctor (SheafOfModules.unit X.ringCatSheaf) f).map g.op
        (hilbertToStructureSheafQuotientAt f T I) := by
  change ⟦IdealSheafData.toStructureSheafQuotientData
      (I.1.comap ((Over.pullback f).map g).left) (I.2.comap g)⟧ =
    ⟦(I.1.toStructureSheafQuotientData I.2).pullback g⟧
  apply Quotient.sound
  apply Modules.QuotientPullbackData.r_of_idealSheafData_eq
  rw [IdealSheafData.idealSheafData_toStructureSheafQuotientData]
  rw [Modules.QuotientPullbackData.idealSheafData_pullback]
  rw [IdealSheafData.idealSheafData_toStructureSheafQuotientData]

/-- After lifting the smaller value universe of the Hilbert functor, Hilbert
families are naturally isomorphic to quotients of the structure sheaf. -/
noncomputable def hilbertStructureSheafQuotientNatIso
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    hilbFunctor f ⋙ uliftFunctor.{u + 1, u} ≅
      quotFunctor (SheafOfModules.unit X.ringCatSheaf) f :=
  NatIso.ofComponents
    (fun T ↦ ((Equiv.ulift.{u + 1, u}).trans
      (hilbertStructureSheafQuotientEquiv f (unop T))).toIso)
    (fun {T T'} g ↦ by
      ext z
      change hilbertToStructureSheafQuotientAt f (unop T')
          ((hilbFunctor f).map g z.down) =
        (quotFunctor (SheafOfModules.unit X.ringCatSheaf) f).map g
          (hilbertToStructureSheafQuotientAt f (unop T) z.down)
      exact hilbertToStructureSheafQuotientAt_naturality
        f g.unop z.down)

end Scheme

end AlgebraicGeometry
