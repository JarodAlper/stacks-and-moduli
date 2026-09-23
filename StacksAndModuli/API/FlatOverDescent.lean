module

public import StacksAndModuli.API.EtaleAffineRefinement
public import StacksAndModuli.API.QuasicoherentFamilies
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Descent of relative flatness

This file develops the affine faithfully-flat reflection step and the étale-locality
of the relative-flatness property used by the moduli prestacks of sheaves.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry

/-- Relative flatness of a quasicoherent module is preserved by pullback in a
cartesian square. -/
lemma Scheme.Modules.FlatOver.pullback_of_isPullback
    {P W T Z : Scheme.{u}} (fst : P ⟶ W) (snd : P ⟶ T)
    (f : W ⟶ Z) (g : T ⟶ Z) (H : IsPullback fst snd f g)
    (M : W.Modules) [M.IsQuasicoherent] (hM : M.FlatOver f) :
    ((Scheme.Modules.pullback fst).obj M).FlatOver snd := by
  let N := (Scheme.Modules.pullback fst).obj M
  intro U V hUV
  apply Scheme.Modules.FlatOver.flat_sections_affine_of_pointwise_basicOpen snd N U V hUV
  intro q hqU
  obtain ⟨A, B, C, hA, hB, hBV, r, s, hrs, hqr⟩ :=
    exists_common_basicOpen_affineOpenPullbackMapOfIsPullback
      fst snd f g H U V q hqU (hUV hqU)
  refine ⟨r, hqr, ?_⟩
  let hsV : P.basicOpen s ≤ snd ⁻¹ᵁ V.1 := by
    intro y hy
    have hyRange := P.basicOpen_le s hy
    exact hBV ((opensRange_affineOpenPullbackMapOfIsPullback_le
      fst snd f g H A B C hA hB hyRange).2)
  have hflatS :
      letI := Module.compHom Γ(N, P.basicOpen s)
        (snd.appLE V.1 (P.basicOpen s) hsV).hom
      Module.Flat Γ(T, V.1) Γ(N, P.basicOpen s) :=
    Scheme.Modules.FlatOver.affineOpenPullback_ambient_basicOpen_of_le
      fst snd f g H hM A B V C hA hB hBV s
  let hrV : P.basicOpen r ≤ snd ⁻¹ᵁ V.1 :=
    (P.basicOpen_le r).trans hUV
  have htransport :
      let d' : Γ(T, V.1) →+* Γ(P, P.basicOpen r) :=
        hrs.symm ▸ (snd.appLE V.1 (P.basicOpen s) hsV).hom
      letI := Module.compHom Γ(N, P.basicOpen r) d'
      Module.Flat Γ(T, V.1) Γ(N, P.basicOpen r) :=
    Scheme.Modules.sections_flat_of_eq N _ _ hrs.symm
      (snd.appLE V.1 (P.basicOpen s) hsV).hom hflatS
  apply Module.Flat.compHom_congr
    (hrs.symm ▸ (snd.appLE V.1 (P.basicOpen s) hsV).hom)
    (snd.appLE V.1 (P.basicOpen r) hrV).hom
  · exact Scheme.Hom.appLE_hom_transport snd V.1 _ _ hrs.symm hsV hrV
  · exact htransport

/-- In a pushout square of coordinate rings, relative flatness of the pulled-back
quasicoherent module reflects across a faithfully flat base map. -/
lemma flat_pullbackQuasicoherentSections_reflects_of_ring_isPushout
    {R S A B : CommRingCat.{u}} (f : R ⟶ A) (g : R ⟶ S)
    (fst : A ⟶ B) (snd : S ⟶ B) (h : IsPushout f g fst snd)
    (M : (Spec A).Modules) [M.IsQuasicoherent]
    (hfaithful : g.hom.FaithfullyFlat)
    (hflat :
      let N := moduleSpecΓFunctor.obj
        ((Scheme.Modules.pullback (Spec.map fst)).obj M)
      letI := Module.compHom N snd.hom
      Module.Flat S N) :
    letI := Module.compHom (moduleSpecΓFunctor.obj M) f.hom
    Module.Flat R (moduleSpecΓFunctor.obj M) := by
  letI : Algebra R A := f.hom.toAlgebra
  letI : Algebra R S := g.hom.toAlgebra
  letI : Algebra A B := fst.hom.toAlgebra
  letI : Algebra S B := snd.hom.toAlgebra
  letI : Algebra R B := (fst.hom.comp f.hom).toAlgebra
  letI : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hw : fst.hom.comp f.hom = snd.hom.comp g.hom :=
    congrArg CommRingCat.Hom.hom h.w
  letI : IsScalarTower R S B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ DFunLike.congr_fun hw x
  have hp : IsPushout
      (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (algebraMap S B)) (CommRingCat.ofHom (algebraMap A B)) := by
    change IsPushout g f snd fst
    exact h.flip
  letI : Algebra.IsPushout R S A B :=
    CommRingCat.isPushout_iff_isPushout.mp hp
  let Q := moduleSpecΓFunctor.obj M
  letI : Module R Q := Module.compHom Q f.hom
  letI : IsScalarTower R A Q :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let N := moduleSpecΓFunctor.obj
    ((Scheme.Modules.pullback (Spec.map fst)).obj M)
  letI : Module S N := Module.compHom N snd.hom
  letI : Module.Flat S N := hflat
  letI : Module.FaithfullyFlat R S := by
    apply RingHom.faithfullyFlat_algebraMap_iff.mp
    exact hfaithful
  let T := (ModuleCat.extendScalars (algebraMap A B)).obj Q
  letI : Module S T := Module.compHom T (algebraMap S B)
  letI : IsScalarTower S B T :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let B' := (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)
  letI : IsScalarTower A B B' :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eB : B' ≃ₗ[B] B :=
    { toEquiv := Equiv.refl _
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let eB' := TensorProduct.AlgebraTensorModule.congr eB
    (LinearEquiv.refl A Q)
  letI : Module S (TensorProduct A B' Q) :=
    Module.compHom _ (algebraMap S B)
  letI : IsScalarTower S B (TensorProduct A B' Q) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let eT : T ≃ₗ[S] TensorProduct A B Q := eB'.restrictScalars S
  let ePullB := pullbackQuasicoherentSectionsLinearEquiv fst M
  let ePull : N ≃ₗ[S] T :=
    { toEquiv := ePullB.toEquiv
      map_add' := ePullB.map_add
      map_smul' := fun s x ↦ by
        change ePullB ((algebraMap S B s) • x) =
          (algebraMap S B s) • ePullB x
        exact ePullB.map_smul (algebraMap S B s) x }
  let e : N ≃ₗ[S] TensorProduct R S Q :=
    ePull.trans eT |>.trans (Algebra.IsPushout.cancelBaseChange R S A B Q)
  letI : Module.Flat S (TensorProduct R S Q) :=
    Module.Flat.of_linearEquiv e.symm
  exact Module.Flat.of_flat_tensorProduct R Q S

/-- For a cartesian square of affine schemes, relative flatness of affine global
sections reflects across a flat surjective base morphism. -/
lemma flat_pullbackQuasicoherentSections_reflects_of_scheme_isPullback
    {P X Y Z : Scheme.{u}} [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine Z]
    (fst : P ⟶ X) (snd : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (h : IsPullback fst snd f g) [Flat g] [Surjective g]
    (M : X.Modules) [M.IsQuasicoherent]
    (hflat :
      let N := (Scheme.Modules.pullback fst).obj M
      letI := Module.compHom Γ(N, ⊤) snd.appTop.hom
      Module.Flat Γ(Y, ⊤) Γ(N, ⊤)) :
    letI := Module.compHom Γ(M, ⊤) f.appTop.hom
    Module.Flat Γ(Z, ⊤) Γ(M, ⊤) := by
  let N := (Scheme.Modules.pullback fst).obj M
  let Nspec := (Scheme.Modules.pullback P.isoSpec.inv).obj N
  have hNspec :
      letI := Module.compHom (moduleSpecΓFunctor.obj Nspec) snd.appTop.hom
      Module.Flat Γ(Y, ⊤) (moduleSpecΓFunctor.obj Nspec) :=
    Scheme.Modules.moduleSpecΓFunctor_pullback_isoSpec_inv_flat_restrictScalars
      N snd.appTop.hom hflat
  let Mspec := (Scheme.Modules.pullback X.isoSpec.inv).obj M
  letI : Mspec.IsQuasicoherent := by
    let e := (Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.inv).app M
    exact (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      e inferInstance
  let Aff := (Scheme.Modules.pullback (Spec.map fst.appTop)).obj Mspec
  let e : Aff ≅ Nspec := pullbackAffineIsoSpecIso fst M
  have hAff :
      letI := Module.compHom (moduleSpecΓFunctor.obj Aff) snd.appTop.hom
      Module.Flat Γ(Y, ⊤) (moduleSpecΓFunctor.obj Aff) := by
    letI : Algebra Γ(Y, ⊤) Γ(P, ⊤) := snd.appTop.hom.toAlgebra
    letI : Module Γ(Y, ⊤) (moduleSpecΓFunctor.obj Nspec) :=
      Module.compHom (moduleSpecΓFunctor.obj Nspec) snd.appTop.hom
    letI : Module.Flat Γ(Y, ⊤) (moduleSpecΓFunctor.obj Nspec) := hNspec
    letI : Module Γ(Y, ⊤) (moduleSpecΓFunctor.obj Aff) :=
      Module.compHom (moduleSpecΓFunctor.obj Aff) snd.appTop.hom
    letI : IsScalarTower Γ(Y, ⊤) Γ(P, ⊤) (moduleSpecΓFunctor.obj Aff) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    letI : IsScalarTower Γ(Y, ⊤) Γ(P, ⊤) (moduleSpecΓFunctor.obj Nspec) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact Module.Flat.of_linearEquiv
      ((moduleSpecΓFunctor.mapIso e).toLinearEquiv.restrictScalars Γ(Y, ⊤))
  have hring : IsPushout f.appTop g.appTop fst.appTop snd.appTop :=
    isPushout_appTop_of_isPullback h
  have hfaithful : g.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
      ⟨inferInstance, inferInstance⟩
  have hMspec :
      letI := Module.compHom (moduleSpecΓFunctor.obj Mspec) f.appTop.hom
      Module.Flat Γ(Z, ⊤) (moduleSpecΓFunctor.obj Mspec) :=
    flat_pullbackQuasicoherentSections_reflects_of_ring_isPushout
      f.appTop g.appTop fst.appTop snd.appTop hring Mspec hfaithful hAff
  exact Scheme.Modules.flat_sections_of_moduleSpecΓFunctor_pullback_isoSpec_inv
    M f.appTop.hom hMspec

/-- Transporting both opens in an `appLE` coefficient homomorphism gives the
coefficient homomorphism for the transported inclusions. -/
lemma Scheme.Hom.appLE_hom_transport_both
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U U' : Y.Opens) (hU : U = U') (V V' : X.Opens) (hV : V = V')
    (e : V ≤ f ⁻¹ᵁ U) (e' : V' ≤ f ⁻¹ᵁ U') :
    hV ▸ ((f.appLE U V e).hom.comp
      (Y.presheaf.map (eqToHom hU).op).hom) =
      (f.appLE U' V' e').hom := by
  subst U'
  subst V'
  simp

/-- Affine sections reflect relative flatness from an affine faithfully-flat
refinement of an étale base chart. -/
lemma Scheme.Modules.FlatOver.flat_sections_affine_of_affine_etale_refinement
    {W T Z : Scheme.{u}} (g : W ⟶ T) (M : W.Modules) [M.IsQuasicoherent]
    (U : W.affineOpens) (V : T.affineOpens) (hUV : U.1 ≤ g ⁻¹ᵁ V.1)
    (q : Z ⟶ V.1.toScheme) [IsAffine Z] [Etale q] [Surjective q]
    (hflat :
      let qT := q ≫ V.1.ι
      let N := (Scheme.Modules.pullback (pullback.fst g qT)).obj M
      N.FlatOver (pullback.snd g qT)) :
    letI := Module.compHom Γ(M, U.1) (g.appLE V.1 U.1 hUV).hom
    Module.Flat Γ(T, V.1) Γ(M, U.1) := by
  let qT := q ≫ V.1.ι
  let P := Limits.pullback g qT
  let fst : P ⟶ W := pullback.fst g qT
  let snd : P ⟶ Z := pullback.snd g qT
  let H : IsPullback fst snd g qT := IsPullback.of_hasPullback g qT
  let B : Z.affineOpens := ⟨⊤, isAffineOpen_top Z⟩
  letI : IsAffine U.1.toScheme := U.2
  letI : IsAffine V.1.toScheme := V.2
  letI : IsAffine B.1.toScheme := B.2
  have hB : B.1 ≤ qT ⁻¹ᵁ V.1 := by
    intro z _
    change V.1.ι (q z) ∈ V.1
    exact (q z).2
  let gU := g.resLE V.1 U.1 hUV
  let qB := qT.resLE V.1 B.1 hB
  let L := affineOpenPullback g qT U B V hUV hB
  letI : IsAffine L := by
    dsimp [L, affineOpenPullback]
    infer_instance
  let i : L ⟶ P :=
    affineOpenPullbackMapOfIsPullback fst snd g qT H U B V hUV hB
  let N := (Scheme.Modules.pullback fst).obj M
  let Q := (Scheme.Modules.pullback i).obj N
  have hQ : Q.FlatOver (pullback.snd gU qB) := by
    apply Scheme.Modules.FlatOver.pullback_isOpenImmersion_of_comm
      i B.1.ι N
    · exact affineOpenPullbackMapOfIsPullback_snd
        fst snd g qT H U B V hUV hB
    · exact hflat
  let MU := (Scheme.Modules.pullback U.1.ι).obj M
  let Q' := (Scheme.Modules.pullback (pullback.fst gU qB)).obj MU
  let e : Q ≅ Q' :=
    affineOpenPullbackSheafIso fst snd g qT H U B V hUV hB M
  have hQ' : Q'.FlatOver (pullback.snd gU qB) :=
    Scheme.Modules.FlatOver.of_iso e hQ
  let Ltop : L.affineOpens := ⟨⊤, isAffineOpen_top L⟩
  let Btop : B.1.toScheme.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have htop : Ltop.1 ≤ pullback.snd gU qB ⁻¹ᵁ Btop.1 := le_top
  have hsectionsRaw := hQ' Ltop Btop htop
  have hsections :
      letI := Module.compHom Γ(Q', ⊤) (pullback.snd gU qB).appTop.hom
      Module.Flat Γ(B.1, ⊤) Γ(Q', ⊤) := by
    apply Module.Flat.compHom_congr _ (pullback.snd gU qB).appTop.hom _ hsectionsRaw
    ext r
    change (L.presheaf.map (homOfLE htop).op).hom
      ((pullback.snd gU qB).appTop.hom r) =
        (pullback.snd gU qB).appTop.hom r
    rw [show L.presheaf.map (homOfLE htop).op = 𝟙 _ by
      rw [← L.presheaf.map_id]
      exact congrArg L.presheaf.map (Subsingleton.elim _ _)]
    rfl
  letI : Surjective qB := by
    constructor
    intro y
    obtain ⟨z, hz⟩ := Surjective.surj (f := q) y
    let z' : B.1.toScheme := ⟨z, Set.mem_univ z⟩
    refine ⟨z', ?_⟩
    apply Subtype.ext
    simpa [qB, qT, z'] using hz
  have hMU :
      letI := Module.compHom Γ(MU, ⊤) gU.appTop.hom
      Module.Flat Γ(V.1, ⊤) Γ(MU, ⊤) :=
    flat_pullbackQuasicoherentSections_reflects_of_scheme_isPullback
      (pullback.fst gU qB) (pullback.snd gU qB) gU qB
      (IsPullback.of_hasPullback gU qB) MU hsections
  let eV := V.1.topIso.commRingCatIsoToRingEquiv.symm
  let b : Γ(T, V.1) →+* Γ(U.1, ⊤) := gU.appTop.hom.comp eV.toRingHom
  have hMU' :
      letI := Module.compHom Γ(MU, ⊤) b
      Module.Flat Γ(T, V.1) Γ(MU, ⊤) :=
    (Module.Flat.compHom_ringEquiv_iff eV b gU.appTop.hom rfl).mpr hMU
  have himage : U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens) = U.1 :=
    U.1.ι_image_top
  let a : Γ(T, V.1) →+* Γ(W, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) :=
    (U.1.ι.appIso ⊤).inv.hom.comp b
  have ha :
      letI := Module.compHom Γ(M, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) a
      Module.Flat Γ(T, V.1) Γ(M, U.1.ι ''ᵁ (⊤ : U.1.toScheme.Opens)) :=
    Scheme.Modules.sections_flat_of_pullback_openImmersion U.1.ι M ⊤ b hMU'
  have htransport :
      let a' : Γ(T, V.1) →+* Γ(W, U.1) := himage ▸ a
      letI := Module.compHom Γ(M, U.1) a'
      Module.Flat Γ(T, V.1) Γ(M, U.1) :=
    Scheme.Modules.sections_flat_of_eq M _ _ himage a ha
  apply Module.Flat.compHom_congr (himage ▸ a) (g.appLE V.1 U.1 hUV).hom
  · ext r
    have hUtransport (s : Γ(U.1, ⊤)) :
        himage ▸ (U.1.ι.appIso (⊤ : U.1.toScheme.Opens)).inv.hom s =
          U.1.topIso.hom.hom s := by
      simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
      exact (Scheme.presheafMap_eq_transport _ _ himage s).symm
    have hcat : V.1.topIso.inv ≫ gU.appTop ≫ U.1.topIso.hom =
        g.appLE V.1 U.1 hUV := by
      rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
      simp
    have hcore : (U.1.topIso.hom.hom.comp gU.appTop.hom).comp
        V.1.topIso.inv.hom =
          (g.appLE V.1 U.1 hUV).hom := by
      simpa only [CommRingCat.hom_comp] using congrArg CommRingCat.Hom.hom hcat
    rw [Scheme.ringHom_transport_apply]
    dsimp [a]
    rw [hUtransport]
    exact RingHom.congr_fun hcore r
  · exact htransport

/-- A relatively flat pullback on an arbitrary cartesian model of a fiber product
transfers to the chosen categorical pullback. -/
lemma Scheme.Modules.FlatOver.canonical_pullback_of_isPullback
    {P W T Z : Scheme.{u}} (fst : P ⟶ W) (snd : P ⟶ T)
    (f : W ⟶ Z) (g : T ⟶ Z) (H : IsPullback fst snd f g)
    (M : W.Modules)
    (hM : ((Scheme.Modules.pullback fst).obj M).FlatOver snd) :
    ((Scheme.Modules.pullback (pullback.fst f g)).obj M).FlatOver
      (pullback.snd f g) := by
  let e := H.isoPullback
  have hPullback :
      ((Scheme.Modules.pullback e.inv).obj
        ((Scheme.Modules.pullback fst).obj M)).FlatOver (pullback.snd f g) :=
    FlatOver.pullback_isIso e.inv ((Scheme.Modules.pullback fst).obj M)
      H.isoPullback_inv_snd hM
  exact FlatOver.of_iso
    (Scheme.Modules.pullbackPullbackIsoOfEq e.inv fst (pullback.fst f g)
      H.isoPullback_inv_fst M)
    hPullback

/-- Relative flatness of a quasicoherent module descends from an étale covering
sieve on the base. -/
lemma Scheme.Modules.FlatOver.of_etale_sieve
    {W T : Scheme.{u}} (g : W ⟶ T) (M : W.Modules) [M.IsQuasicoherent]
    (R : Sieve T) (hR : R ∈ Scheme.etaleTopology T)
    (hM : ∀ f : R.arrows.category,
      let q := f.obj.hom
      let N := (Scheme.Modules.pullback (pullback.fst g q)).obj M
      N.FlatOver (pullback.snd g q)) :
    M.FlatOver g := by
  classical
  obtain ⟨R₀, hR₀, hR₀R⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hR
  obtain ⟨𝒰, h𝒰eq⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hR₀
  intro U V hUV
  apply Scheme.Modules.FlatOver.flat_sections_affine_of_pointwise_basicOpen g M U V hUV
  intro p hpU
  have hpV : g p ∈ V.1 := hUV hpU
  obtain ⟨i, x, hx⟩ := Scheme.Cover.exists_eq 𝒰 (g p)
  let f : 𝒰.X i ⟶ T := 𝒰.f i
  letI : Etale f :=
    (Scheme.ofArrows_mem_precoverage_iff (@Etale) |>.mp 𝒰.mem₀).2 i
  have hfR : R f := by
    apply hR₀R
    rw [h𝒰eq]
    exact ⟨i⟩
  let O : T.Opens := ⟨Set.range f, f.isOpenMap.isOpen_range⟩
  have hpO : g p ∈ O := ⟨x, hx⟩
  obtain ⟨_, ⟨V₀, hV₀aff, rfl⟩, hpV₀, hV₀le⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open
      (a := g p) (show g p ∈ V.1 ⊓ O from ⟨hpV, hpO⟩) (V.1 ⊓ O).isOpen
  let V₀a : T.affineOpens := ⟨V₀, hV₀aff⟩
  letI : IsAffine V₀a.1.toScheme := V₀a.2
  let f₀ := f ∣_ V₀
  letI : Etale f₀ := MorphismProperty.of_isPullback
    (isPullback_morphismRestrict f V₀).flip inferInstance
  letI : Surjective f₀ := by
    constructor
    intro y
    have hyO : V₀a.1.ι y ∈ O := (hV₀le y.2).2
    obtain ⟨z, hz⟩ := hyO
    have hzV₀ : f z ∈ V₀ := hz ▸ y.2
    let z' : (f ⁻¹ᵁ V₀).toScheme := ⟨z, hzV₀⟩
    refine ⟨z', ?_⟩
    apply Subtype.ext
    simpa [f₀, z'] using hz
  obtain ⟨Z, hZaff, q, hqEt, hqSurj, e, he⟩ :=
    Scheme.exists_affine_etale_surjective_refinement f₀
  letI : IsAffine Z := hZaff
  letI : Etale q := hqEt
  letI : Surjective q := hqSurj
  let qT : Z ⟶ T := q ≫ V₀a.1.ι
  have hqTf : (e ≫ (f ⁻¹ᵁ V₀).ι) ≫ f = qT := by
    rw [Category.assoc, ← morphismRestrict_ι]
    rw [← Category.assoc, he]
  have hqR : R qT := by
    have := R.downward_closed hfR (e ≫ (f ⁻¹ᵁ V₀).ι)
    rwa [hqTf] at this
  let fq : R.arrows.category := R.arrows.categoryMk qT hqR
  have hflatq :
      let N := (Scheme.Modules.pullback (pullback.fst g qT)).obj M
      N.FlatOver (pullback.snd g qT) := hM fq
  have hpV₀' : g p ∈ V₀ := hpV₀
  let p' : (g ⁻¹ᵁ V₀) := ⟨p, hpV₀'⟩
  obtain ⟨r, hrle, hpr⟩ :=
    U.2.exists_basicOpen_le p' hpU
  let U₀ : W.affineOpens := W.affineBasicOpen r
  have hU₀V₀ : U₀.1 ≤ g ⁻¹ᵁ V₀ := hrle
  have hlocal₀ :
      letI := Module.compHom Γ(M, U₀.1) (g.appLE V₀ U₀.1 hU₀V₀).hom
      Module.Flat Γ(T, V₀) Γ(M, U₀.1) :=
    Scheme.Modules.FlatOver.flat_sections_affine_of_affine_etale_refinement
      g M U₀ V₀a hU₀V₀ q hflatq
  have hV₀V : V₀ ≤ V.1 := hV₀le.trans inf_le_left
  let hId : V₀ ≤ (𝟙 T : T ⟶ T) ⁻¹ᵁ V.1 := by simpa using hV₀V
  let a : Γ(T, V.1) →+* Γ(T, V₀) :=
    ((𝟙 T : T ⟶ T).appLE V.1 V₀ hId).hom
  let b : Γ(T, V₀) →+* Γ(W, U₀.1) := (g.appLE V₀ U₀.1 hU₀V₀).hom
  have ha : a.Flat := (𝟙 T : T ⟶ T).flat_appLE V.2 hV₀aff hId
  letI : Algebra Γ(T, V.1) Γ(T, V₀) := a.toAlgebra
  letI : Module.Flat Γ(T, V.1) Γ(T, V₀) := ha
  letI : Module Γ(T, V₀) Γ(M, U₀.1) := Module.compHom Γ(M, U₀.1) b
  letI : Module.Flat Γ(T, V₀) Γ(M, U₀.1) := hlocal₀
  letI : Module Γ(T, V.1) Γ(M, U₀.1) :=
    Module.compHom Γ(M, U₀.1) (b.comp a)
  letI : IsScalarTower Γ(T, V.1) Γ(T, V₀) Γ(M, U₀.1) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have htrans : Module.Flat Γ(T, V.1) Γ(M, U₀.1) :=
    Module.Flat.trans Γ(T, V.1) Γ(T, V₀) Γ(M, U₀.1)
  let hU₀V : U₀.1 ≤ g ⁻¹ᵁ V.1 := hrle.trans (g.preimage_mono hV₀V)
  refine ⟨r, hpr, ?_⟩
  change
    letI := Module.compHom Γ(M, U₀.1) (g.appLE V.1 U₀.1 hU₀V).hom
    Module.Flat Γ(T, V.1) Γ(M, U₀.1)
  apply Module.Flat.compHom_congr (b.comp a)
    (g.appLE V.1 U₀.1 hU₀V).hom
  · ext s
    change (((𝟙 T : T ⟶ T).appLE V.1 V₀ hId ≫
      g.appLE V₀ U₀.1 hU₀V₀).hom) s = _
    rw [Scheme.Hom.appLE_comp_appLE]
    simp
  · exact htrans

end AlgebraicGeometry
