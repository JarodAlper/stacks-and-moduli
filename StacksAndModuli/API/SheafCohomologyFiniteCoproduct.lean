module

public import StacksAndModuli.API.SheafCohomologyOpenMayerVietoris
public import StacksAndModuli.API.SheafCohomologySchemeIso
public import StacksAndModuli.API.SheafCohomologyLES
public import StacksAndModuli.API.FlasqueVanishing
public import StacksAndModuli.API.FiniteCoproductGlobalSections
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# First cohomology of finite coproducts of schemes

Sheaf cohomology preserves finite coproducts.  For module sheaves on a fixed scheme,
this immediately transfers cohomology vanishing from the summands to their coproduct.
For a finite coproduct of schemes over a field, the first structure-sheaf cohomology is
the product of the first cohomology spaces of its summands.  The latter proof first
obtains a linear Mayer--Vietoris splitting for two complementary open subschemes,
including the scalar-compatibility comparison between cohomology on an ambient open and
on the associated open subscheme, and then inducts over a finite indexing type.

## Main results

* `AlgebraicGeometry.Scheme.Modules.subsingleton_H_coproduct_of_finite`: finite
  coproducts preserve vanishing of module-sheaf cohomology.
* `AlgebraicGeometry.Scheme.structureCohomologySigmaOneLinearEquiv`: the linear
  decomposition of first cohomology for a finite coproduct.
* `AlgebraicGeometry.Scheme.finiteDimensional_structureCohomologySigmaOne`: finite
  dimensionality transfers from the summands to their finite coproduct.
* `AlgebraicGeometry.Scheme.Modules.h_structureModule_sigma_one_eq_sum`: the resulting
  sum formula for first-cohomology dimensions.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
  TopologicalSpace Opposite

universe u v₁ v₂ u₁ u₂

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A finite coproduct of module sheaves has vanishing `i`-th cohomology when every
summand does. -/
theorem subsingleton_H_coproduct_of_finite
    {J : Type u} [Finite J] (F : J → X.Modules) (i : ℕ)
    (h : ∀ j, Subsingleton
      (((SheafOfModules.toSheaf _).obj (F j)).H i)) :
    Subsingleton
      (((SheafOfModules.toSheaf _).obj (∐ F)).H i) := by
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf ⋙
    CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) i
  have hzero : IsZero (Discrete.functor F ⋙ T) := by
    apply Functor.isZero
    rintro ⟨j⟩
    exact AddCommGrpCat.isZero_iff_subsingleton.mpr (h j)
  have hcolim : IsZero (colimit (Discrete.functor F ⋙ T)) :=
    (colimit.isColimit _).isZero_pt hzero
  have hleft : IsZero (T.obj (∐ F)) :=
    hcolim.of_iso (preservesColimitIso T (Discrete.functor F))
  exact AddCommGrpCat.isZero_iff_subsingleton.mp hleft

end AlgebraicGeometry.Scheme.Modules

namespace CategoryTheory.Functor

/-- An additive functor induces a ring homomorphism between endomorphism rings. -/
noncomputable def mapEndRingHom
    {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
    [Preadditive A] [Preadditive B] (G : A ⥤ B) [G.Additive] (X : A) :
    End X →+* End (G.obj X) where
  toMonoidHom := G.mapEnd X
  map_zero' := G.map_zero X X
  map_add' := by
    intro x y
    exact G.map_add

end CategoryTheory.Functor

namespace CategoryTheory.Sheaf

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasWeakSheafify J (Type u)] [HasSheafify J AddCommGrpCat.{u}]
  [HasWeakSheafify K (Type u)] [HasSheafify K AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]
  [HasExt.{u} (Sheaf K AddCommGrpCat.{u})]

/-- An additive equivalence of sheaf categories preserving the constant integer sheaf
induces an additive equivalence on sheaf cohomology. -/
noncomputable def HAddEquivOfEquivalence
    (E : Sheaf J AddCommGrpCat.{u} ≌ Sheaf K AddCommGrpCat.{u})
    [E.functor.Additive]
    (c : (constantSheaf K AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ)) ≅
      E.functor.obj ((constantSheaf J AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))))
    (F : Sheaf J AddCommGrpCat.{u}) (n : ℕ) :
    F.H n ≃+ (E.functor.obj F).H n := by
  let mapEquiv : Abelian.Ext
      ((constantSheaf J AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))) F n ≃+
      Abelian.Ext
        (E.functor.obj ((constantSheaf J AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ)))) (E.functor.obj F) n :=
    AddEquiv.ofBijective
      (E.functor.mapExtAddHom _ _ n)
      (E.functor.mapExt_bijective_of_preservesInjectiveObjects _ _ n)
  exact mapEquiv.trans (Abelian.Ext.isoAddEquiv c.symm (Iso.refl _) n)

/-- An additive equivalence of sheaf categories, together with identifications of the
constant integer sheaf and the target sheaf, induces an additive cohomology equivalence. -/
noncomputable def HAddEquivOfEquivalenceOfIso
    (E : Sheaf J AddCommGrpCat.{u} ≌ Sheaf K AddCommGrpCat.{u})
    [E.functor.Additive]
    (c : (constantSheaf K AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ)) ≅
      E.functor.obj ((constantSheaf J AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))))
    {F : Sheaf J AddCommGrpCat.{u}} {G : Sheaf K AddCommGrpCat.{u}}
    (eF : E.functor.obj F ≅ G) (n : ℕ) : F.H n ≃+ G.H n := by
  let mapEquiv : Abelian.Ext
      ((constantSheaf J AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))) F n ≃+
      Abelian.Ext
        (E.functor.obj ((constantSheaf J AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift ℤ)))) (E.functor.obj F) n :=
    AddEquiv.ofBijective
      (E.functor.mapExtAddHom _ _ n)
      (E.functor.mapExt_bijective_of_preservesInjectiveObjects _ _ n)
  exact mapEquiv.trans (Abelian.Ext.isoAddEquiv c.symm eF n)

omit [HasWeakSheafify J (Type u)] [HasWeakSheafify K (Type u)] in
/-- Evaluation of `HAddEquivOfEquivalenceOfIso` is the map on Ext followed by the
specified source and target isomorphisms. -/
@[simp]
lemma HAddEquivOfEquivalenceOfIso_apply
    (E : Sheaf J AddCommGrpCat.{u} ≌ Sheaf K AddCommGrpCat.{u})
    [E.functor.Additive]
    (c : (constantSheaf K AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ)) ≅
      E.functor.obj ((constantSheaf J AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))))
    {F : Sheaf J AddCommGrpCat.{u}} {G : Sheaf K AddCommGrpCat.{u}}
    (eF : E.functor.obj F ≅ G) (n : ℕ) (x : F.H n) :
    HAddEquivOfEquivalenceOfIso E c eF n x =
      Abelian.Ext.isoAddEquiv c.symm eF n
        (x.mapExactFunctor E.functor) := rfl

/-- A scalar-compatible additive equivalence of sheaf categories induces a linear
equivalence on sheaf cohomology. -/
noncomputable def HLinearEquivOfEquivalenceOfIso
    {R : Type u} [Semiring R]
    (E : Sheaf J AddCommGrpCat.{u} ≌ Sheaf K AddCommGrpCat.{u})
    [E.functor.Additive]
    (c : (constantSheaf K AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ)) ≅
      E.functor.obj ((constantSheaf J AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ))))
    {F : Sheaf J AddCommGrpCat.{u}} {G : Sheaf K AddCommGrpCat.{u}}
    (eF : E.functor.obj F ≅ G) (phi : R →+* End F)
    (psi : R →+* End G)
    (hpsi : ∀ r, E.functor.map (phi r) ≫ eF.hom = eF.hom ≫ psi r)
    (n : ℕ) :
    letI : Module R (F.H n) := Abelian.Ext.moduleOfRingHom phi n
    letI : Module R (G.H n) := Abelian.Ext.moduleOfRingHom psi n
    F.H n ≃ₗ[R] G.H n := by
  letI : Module R (F.H n) := Abelian.Ext.moduleOfRingHom phi n
  letI : Module R (G.H n) := Abelian.Ext.moduleOfRingHom psi n
  exact AddEquiv.toLinearEquiv
    (HAddEquivOfEquivalenceOfIso E c eF n) (by
      intro r x
      simp only [Abelian.Ext.moduleOfRingHom_smul,
        HAddEquivOfEquivalenceOfIso_apply, Abelian.Ext.isoAddEquiv_apply,
        Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
        Abelian.Ext.comp_assoc_of_second_deg_zero,
        Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀]
      exact congrArg
        (fun q ↦
          (Abelian.Ext.mk₀ c.hom).comp
            ((x.mapExactFunctor E.functor).comp
              (Abelian.Ext.mk₀ q) (add_zero n)) (zero_add n))
        (hpsi r))

/-- Restriction in the cohomology presheaf is linear for a scalar action induced by
endomorphisms of the original sheaf. -/
noncomputable def HPrimeMapLinear
    {R : Type u} [Semiring R] (F : Sheaf J AddCommGrpCat.{u})
    (phi : R →+* End F) (n : ℕ) {U V : C} (i : op U ⟶ op V) :
    letI : Module R (F.H' n U) := Abelian.Ext.moduleOfRingHom phi n
    letI : Module R (F.H' n V) := Abelian.Ext.moduleOfRingHom phi n
    F.H' n U →ₗ[R] F.H' n V := by
  letI : Module R (F.H' n U) := Abelian.Ext.moduleOfRingHom phi n
  letI : Module R (F.H' n V) := Abelian.Ext.moduleOfRingHom phi n
  exact
    { toFun := (F.cohomologyPresheaf n).map i
      map_add' := map_add _
      map_smul' := by
        intro r x
        change (F.cohomologyPresheaf n).map i
            (x.comp (Abelian.Ext.mk₀ (phi r)) (add_zero n)) =
          ((F.cohomologyPresheaf n).map i x).comp
            (Abelian.Ext.mk₀ (phi r)) (add_zero n)
        exact (ConcreteCategory.congr_hom
          (((cohomologyPresheafFunctor J n).map (phi r)).naturality i) x).symm }

end CategoryTheory.Sheaf

namespace CategoryTheory.GrothendieckTopology.MayerVietorisSquare

open Category Opposite Limits Abelian ComposableArrows

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type u)] [HasSheafify J AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]

/-- If degree-zero and degree-one cohomology vanish on the intersection, the
Mayer--Vietoris map identifies degree-one cohomology with a biproduct. -/
noncomputable def HOneAddEquivBiprodOfIntersectionVanishing
    (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{u})
    [Subsingleton (F.H' 0 S.X₁)] [Subsingleton (F.H' 1 S.X₁)] :
    F.H' 1 S.X₄ ≃+ (F.H' 1 S.X₂ × F.H' 1 S.X₃) := by
  let f := S.toBiprod F 1
  have hf₀ : (S.sequence F 0 1 rfl).map' 2 3 = 0 := by
    change S.δ F 0 1 rfl = 0
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp
  have hf₁ : (S.sequence F 0 1 rfl).map' 4 5 = 0 := by
    change S.fromBiprod F 1 = 0
    ext x
    exact Subsingleton.elim _ _
  letI : Mono f :=
    ((S.sequence_exact F 0 1 rfl).exact 2).mono_g hf₀
  letI : Epi f :=
    ((S.sequence_exact F 0 1 rfl).exact 3).epi_f hf₁
  exact (AddEquiv.ofBijective f.hom
    ⟨(AddCommGrpCat.mono_iff_injective f).mp inferInstance,
      (AddCommGrpCat.epi_iff_surjective f).mp inferInstance⟩).trans
        (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv

/-- Linear version of `HOneAddEquivBiprodOfIntersectionVanishing` for a scalar action
induced by endomorphisms of the sheaf. -/
noncomputable def HOneLinearEquivBiprodOfIntersectionVanishing
    {R : Type u} [Semiring R] (S : J.MayerVietorisSquare)
    (F : Sheaf J AddCommGrpCat.{u}) (phi : R →+* End F)
    [Subsingleton (F.H' 0 S.X₁)] [Subsingleton (F.H' 1 S.X₁)] :
    letI : Module R (F.H' 1 S.X₄) := Abelian.Ext.moduleOfRingHom phi 1
    letI : Module R (F.H' 1 S.X₂) := Abelian.Ext.moduleOfRingHom phi 1
    letI : Module R (F.H' 1 S.X₃) := Abelian.Ext.moduleOfRingHom phi 1
    F.H' 1 S.X₄ ≃ₗ[R] (F.H' 1 S.X₂ × F.H' 1 S.X₃) := by
  letI : Module R (F.H' 1 S.X₄) := Abelian.Ext.moduleOfRingHom phi 1
  letI : Module R (F.H' 1 S.X₂) := Abelian.Ext.moduleOfRingHom phi 1
  letI : Module R (F.H' 1 S.X₃) := Abelian.Ext.moduleOfRingHom phi 1
  let f := S.toBiprod F 1
  have hf₀ : (S.sequence F 0 1 rfl).map' 2 3 = 0 := by
    change S.δ F 0 1 rfl = 0
    ext x
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    simp
  have hf₁ : (S.sequence F 0 1 rfl).map' 4 5 = 0 := by
    change S.fromBiprod F 1 = 0
    ext x
    exact Subsingleton.elim _ _
  letI : Mono f :=
    ((S.sequence_exact F 0 1 rfl).exact 2).mono_g hf₀
  letI : Epi f :=
    ((S.sequence_exact F 0 1 rfl).exact 3).epi_f hf₁
  let l : F.H' 1 S.X₄ →ₗ[R] (F.H' 1 S.X₂ × F.H' 1 S.X₃) :=
    { toFun := fun x ↦ (AddCommGrpCat.biprodIsoProd _ _).hom (f x)
      map_add' := by intros; simp
      map_smul' := by
        intro r x
        change (AddCommGrpCat.biprodIsoProd _ _).hom (S.toBiprod F 1 (r • x)) =
          r • (AddCommGrpCat.biprodIsoProd _ _).hom (S.toBiprod F 1 x)
        rw [S.toBiprod_apply, S.toBiprod_apply]
        simp only [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
        change
          ((F.cohomologyPresheaf 1).map S.f₂₄.op (r • x),
            (F.cohomologyPresheaf 1).map S.f₃₄.op (r • x)) =
          (r • (F.cohomologyPresheaf 1).map S.f₂₄.op x,
            r • (F.cohomologyPresheaf 1).map S.f₃₄.op x)
        exact congrArg₂ Prod.mk
          ((CategoryTheory.Sheaf.HPrimeMapLinear F phi 1 S.f₂₄.op).map_smul r x)
          ((CategoryTheory.Sheaf.HPrimeMapLinear F phi 1 S.f₃₄.op).map_smul r x) }
  exact LinearEquiv.ofBijective l ⟨
    (by
      intro x y hxy
      apply (AddCommGrpCat.mono_iff_injective f).mp inferInstance
      apply (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
      exact hxy),
    (by
      intro y
      obtain ⟨z, rfl⟩ :=
        (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.surjective y
      obtain ⟨x, hx⟩ :=
        (AddCommGrpCat.epi_iff_surjective f).mp inferInstance z
      exact ⟨x, congrArg (fun t ↦
        (AddCommGrpCat.biprodIsoProd _ _).hom t) hx⟩)⟩

end CategoryTheory.GrothendieckTopology.MayerVietorisSquare

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type u)] [HasSheafify J AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf J AddCommGrpCat.{u})]

/-- Linear comparison between cohomology on a terminal object and global sheaf
cohomology. -/
noncomputable def HPrimeTerminalLinearEquivH
    {R : Type u} [Semiring R] (F : Sheaf J AddCommGrpCat.{u})
    (phi : R →+* End F) (n : ℕ) {T : C} (hT : IsTerminal T) :
    letI : Module R (F.H' n T) := Abelian.Ext.moduleOfRingHom phi n
    letI : Module R (F.H n) := Abelian.Ext.moduleOfRingHom phi n
    F.H' n T ≃ₗ[R] F.H n := by
  letI : Module R (F.H' n T) := Abelian.Ext.moduleOfRingHom phi n
  letI : Module R (F.H n) := Abelian.Ext.moduleOfRingHom phi n
  exact AddEquiv.toLinearEquiv (HPrimeTerminalEquivH J F n hT) (by
    intro r x
    change (HPrimeTerminalNatIsoH J n hT).hom.app F
        (x.comp (Abelian.Ext.mk₀ (phi r)) (add_zero n)) =
      ((HPrimeTerminalNatIsoH J n hT).hom.app F x).comp
        (Abelian.Ext.mk₀ (phi r)) (add_zero n)
    exact ConcreteCategory.congr_hom
      ((HPrimeTerminalNatIsoH J n hT).hom.naturality (phi r)) x)

/-- Linear comparison between cohomology on an object and global cohomology after
passing to the corresponding over-site. -/
noncomputable def HPrimeOpenLinearEquivH
    {R : Type u} [Semiring R] (F : Sheaf J AddCommGrpCat.{u})
    (phi : R →+* End F) (U : C) (n : ℕ) :
    let G := J.overPullback AddCommGrpCat.{u} U
    letI : Module R (F.H' n U) := Abelian.Ext.moduleOfRingHom phi n
    letI : Module R ((F.over U).H n) := Abelian.Ext.moduleOfRingHom
      ((G.mapEndRingHom F).comp phi) n
    F.H' n U ≃ₗ[R] (F.over U).H n := by
  let G := J.overPullback AddCommGrpCat.{u} U
  letI : Module R (F.H' n U) := Abelian.Ext.moduleOfRingHom phi n
  letI : Module R ((F.over U).H n) := Abelian.Ext.moduleOfRingHom
    ((G.mapEndRingHom F).comp phi) n
  exact AddEquiv.toLinearEquiv (HPrimeOpenEquivH J F U n) (by
    intro r x
    change HPrimeOpenEquivH J F U n
        (x.comp (Abelian.Ext.mk₀ (phi r)) (add_zero n)) =
      (HPrimeOpenEquivH J F U n x).comp
        (Abelian.Ext.mk₀ (G.map (phi r))) (add_zero n)
    exact (HPrimeOpenEquivH_naturality J (phi r) U n x).symm)

end CategoryTheory.Sheaf

namespace CategoryTheory.Sheaf

/-- The equivalence between sheaves on an open subspace and sheaves on the over-site
sends the constant additive sheaf to the constant additive sheaf. -/
noncomputable def constantAddSheafOverIso {X : TopCat.{u}}
    (U : Opens X) (A : AddCommGrpCat.{u}) :
    (constantSheaf (Opens.grothendieckTopology U)
        AddCommGrpCat.{u}).obj A ≅
      U.sheafEquivOver.functor.obj
        ((constantSheaf ((Opens.grothendieckTopology X).over U)
          AddCommGrpCat.{u}).obj A) := by
  let G := U.overEquivalence.inverse
  exact (equivCommuteConstant'
    (Opens.grothendieckTopology U) AddCommGrpCat.{u}
    ((Opens.grothendieckTopology X).over U) G
    (isTerminalTop : IsTerminal (⊤ : Opens U))
    (IsTerminal.isTerminalObj G (⊤ : Opens U) isTerminalTop)).app A

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Scheme

open CategoryTheory

/-- Under the equivalence between sheaves on an open and sheaves on the associated
over-site, the underlying additive sheaf of the restricted structure sheaf is the
underlying additive sheaf of the open subscheme's structure sheaf. -/
noncomputable def structureAddSheafOverIso (X : Scheme.{u}) (U : X.Opens) :
    U.sheafEquivOver.functor.obj
        (((SheafOfModules.toSheaf X.ringCatSheaf).obj
          (structureModule X)).over U) ≅
      (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).obj
        (structureModule U.toScheme) := by
  let e : (Modules.overEquiv U).functor.obj
        ((SheafOfModules.overFunctor X.ringCatSheaf U).obj
          (structureModule X)) ≅
      structureModule U.toScheme :=
    (Modules.overFunctorEquiv U).app (structureModule X) ≪≫
      Modules.restrictUnitIso U.ι
  exact (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).mapIso e

/-- The structure-sheaf comparison over an open subscheme intertwines multiplication
by a global section with multiplication by its restriction. -/
lemma structureAddSheafOverIso_map_smul (X : Scheme.{u}) (U : X.Opens)
    (r : Γ(X, ⊤)) :
    let G := (Opens.grothendieckTopology X).overPullback
      AddCommGrpCat.{u} U
    let E := U.sheafEquivOver (A := AddCommGrpCat.{u})
    E.functor.map (G.map (Modules.smulSheafHom (structureModule X) r)) ≫
        (structureAddSheafOverIso X U).hom =
      (structureAddSheafOverIso X U).hom ≫
        Modules.smulSheafHom (structureModule U.toScheme) (U.ι.appTop r) := by
  dsimp only
  let M := (Modules.overEquiv U).functor.obj
    ((SheafOfModules.overFunctor X.ringCatSheaf U).obj (structureModule X))
  let e : M ≅ structureModule U.toScheme :=
    (Modules.overFunctorEquiv U).app (structureModule X) ≪≫
      Modules.restrictUnitIso U.ι
  change
    (U.sheafEquivOver.functor.map
        (((Opens.grothendieckTopology X).overPullback AddCommGrpCat.{u} U).map
          (Modules.smulSheafHom (structureModule X) r))) ≫
          (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map e.hom =
      (SheafOfModules.toSheaf U.toScheme.ringCatSheaf).map e.hom ≫
        Modules.smulSheafHom (structureModule U.toScheme) (U.ι.appTop r)
  rw [show
    U.sheafEquivOver.functor.map
        (((Opens.grothendieckTopology X).overPullback AddCommGrpCat.{u} U).map
          (Modules.smulSheafHom (structureModule X) r)) =
      Modules.smulSheafHom M (U.ι.appTop r) by
        refine Sheaf.hom_ext (NatTrans.ext (funext fun W ↦ ?_))
        refine ConcreteCategory.hom_ext _ _ fun x ↦ ?_
        simp only [Opens.sheafEquivOver_functor_map_hom_app,
          Functor.sheafPushforwardContinuous_map_hom_app,
          Modules.smulSheafHom_hom, Over.forget_obj,
          Modules.smulNatTrans_app, Modules.restrictTop_apply, Opens.ι_app,
          Opens.map_top, homOfLE_leOfHom, op_unop]
        congr 3
        dsimp only [Modules.restrictTop]
        simp only [Scheme.Opens.toScheme_presheaf_map]
        erw [← ConcreteCategory.comp_apply]
        rw [← X.presheaf.map_comp]
        rfl]
  exact Modules.smulSheafHom_comp e.hom (U.ι.appTop r)

/-- Cohomology of the structure sheaf over an open equals structure-sheaf cohomology
of the associated open subscheme, as additive groups. -/
noncomputable def structureCohomologyOpenAddEquiv
    (X : Scheme.{u}) (U : X.Opens) (n : ℕ) :
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj
      (structureModule X)).H' n U ≃+
      Modules.H (structureModule U.toScheme) n := by
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj
    (structureModule X)
  let E := U.sheafEquivOver (A := AddCommGrpCat.{u})
  letI : E.functor.Additive := ⟨by intros; rfl⟩
  exact (CategoryTheory.Sheaf.HPrimeOpenEquivH
      (Opens.grothendieckTopology X) F U n).trans
    (CategoryTheory.Sheaf.HAddEquivOfEquivalenceOfIso E
      (CategoryTheory.Sheaf.constantAddSheafOverIso U
        (AddCommGrpCat.of (ULift ℤ)))
      (structureAddSheafOverIso X U) n)

/-- Cohomology of the structure sheaf over an open equals structure-sheaf cohomology
of the associated open subscheme, linearly over the base field. -/
noncomputable def structureCohomologyOpenLinearEquiv
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] (U : X.Opens) (n : ℕ) :
    let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj
      (structureModule X)
    let phi := (Modules.smulEnd (structureModule X)).comp
      (X.baseRingHom (CommRingCat.of k))
    letI : Module k (F.H' n U) := Abelian.Ext.moduleOfRingHom phi n
    F.H' n U ≃ₗ[k] Modules.H (structureModule U.toScheme) n := by
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj
    (structureModule X)
  let phi := (Modules.smulEnd (structureModule X)).comp
    (X.baseRingHom (CommRingCat.of k))
  let G := (Opens.grothendieckTopology X).overPullback
    AddCommGrpCat.{u} U
  let E := U.sheafEquivOver (A := AddCommGrpCat.{u})
  let psi := (Modules.smulEnd (structureModule U.toScheme)).comp
    (U.toScheme.baseRingHom (CommRingCat.of k))
  letI : E.functor.Additive := ⟨by intros; rfl⟩
  letI : Module k (F.H' n U) := Abelian.Ext.moduleOfRingHom phi n
  exact (CategoryTheory.Sheaf.HPrimeOpenLinearEquivH F phi U n).trans
    (CategoryTheory.Sheaf.HLinearEquivOfEquivalenceOfIso E
      (CategoryTheory.Sheaf.constantAddSheafOverIso U
        (AddCommGrpCat.of (ULift ℤ)))
      (structureAddSheafOverIso X U) ((G.mapEndRingHom F).comp phi) psi
      (fun a ↦ by
        have hring : Modules.baseRingHom (X ↘ Spec (CommRingCat.of k)) ≫
              U.ι.appTop =
            Modules.baseRingHom (U.toScheme ↘ Spec (CommRingCat.of k)) := by
          rw [Modules.baseRingHom_comp_appTop, U.ι_comp_over]
        have hbase : U.ι.appTop
              (X.baseRingHom (CommRingCat.of k) a) =
            U.toScheme.baseRingHom (CommRingCat.of k) a :=
          ConcreteCategory.congr_hom hring a
        change E.functor.map
              (G.map (Modules.smulSheafHom (structureModule X)
                (X.baseRingHom (CommRingCat.of k) a))) ≫
              (structureAddSheafOverIso X U).hom =
            (structureAddSheafOverIso X U).hom ≫
              Modules.smulSheafHom (structureModule U.toScheme)
                (U.toScheme.baseRingHom (CommRingCat.of k) a)
        rw [← hbase]
        exact structureAddSheafOverIso_map_smul X U
          (X.baseRingHom (CommRingCat.of k) a)) n)

/-- First structure-sheaf cohomology splits over two complementary open subschemes. -/
noncomputable def structureCohomologyComplOpenAddEquiv
    (X : Scheme.{u}) (U V : X.Opens) (h : IsCompl U V) :
    Modules.H (structureModule X) 1 ≃+
      (Modules.H (structureModule U.toScheme) 1 ×
        Modules.H (structureModule V.toScheme) 1) := by
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj
    (structureModule X)
  let S := _root_.Opens.mayerVietorisSquare U V
  have hT : IsTerminal (U ⊔ V) :=
    IsTerminal.ofIso isTerminalTop (eqToIso h.sup_eq_top).symm
  let eT : F.H 1 ≃+ F.H' 1 (U ⊔ V) :=
    (CategoryTheory.Sheaf.HPrimeTerminalIsoH
      (Opens.grothendieckTopology X) F 1 hT).symm.addCommGroupIsoToAddEquiv
  letI : Subsingleton (F.H' 0 (U ⊓ V)) := by
    rw [h.inf_eq_bot]
    exact (CategoryTheory.Sheaf.HPrimeAddEquivZero
      (Opens.grothendieckTopology X) F ⊥).toEquiv.subsingleton_congr.mpr
        (AddCommGrpCat.subsingleton_of_isZero
          (TopCat.Sheaf.isTerminalOfEmpty F).isZero)
  letI : Subsingleton (F.H' 1 (U ⊓ V)) := by
    rw [h.inf_eq_bot]
    letI : Subsingleton (⊥ : X.Opens).toScheme :=
      ⟨fun x _ ↦ False.elim x.property⟩
    exact (structureCohomologyOpenAddEquiv X ⊥ 1).toEquiv.subsingleton_congr.mpr
      (Modules.subsingleton_H_of_subsingleton
        (structureModule (⊥ : X.Opens).toScheme) 0)
  letI : Subsingleton (F.H' 0 S.X₁) := by
    change Subsingleton (F.H' 0 (U ⊓ V))
    infer_instance
  letI : Subsingleton (F.H' 1 S.X₁) := by
    change Subsingleton (F.H' 1 (U ⊓ V))
    infer_instance
  exact eT.trans
    ((S.HOneAddEquivBiprodOfIntersectionVanishing F).trans
        ((structureCohomologyOpenAddEquiv X U 1).prodCongr
          (structureCohomologyOpenAddEquiv X V 1)))

/-- First structure-sheaf cohomology splits linearly over two complementary open
subschemes. -/
noncomputable def structureCohomologyComplOpenLinearEquiv
    (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    (U V : X.Opens) (h : IsCompl U V) :
    Modules.H (structureModule X) 1 ≃ₗ[k]
      (Modules.H (structureModule U.toScheme) 1 ×
        Modules.H (structureModule V.toScheme) 1) := by
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj
    (structureModule X)
  let phi := (Modules.smulEnd (structureModule X)).comp
    (X.baseRingHom (CommRingCat.of k))
  let S := _root_.Opens.mayerVietorisSquare U V
  have hT : IsTerminal (U ⊔ V) :=
    IsTerminal.ofIso isTerminalTop (eqToIso h.sup_eq_top).symm
  letI : Module k (F.H' 1 (U ⊔ V)) :=
    Abelian.Ext.moduleOfRingHom phi 1
  let eT : F.H 1 ≃ₗ[k] F.H' 1 (U ⊔ V) :=
    (CategoryTheory.Sheaf.HPrimeTerminalLinearEquivH F phi 1 hT).symm
  letI : Subsingleton (F.H' 0 (U ⊓ V)) := by
    rw [h.inf_eq_bot]
    exact (CategoryTheory.Sheaf.HPrimeAddEquivZero
      (Opens.grothendieckTopology X) F ⊥).toEquiv.subsingleton_congr.mpr
        (AddCommGrpCat.subsingleton_of_isZero
          (TopCat.Sheaf.isTerminalOfEmpty F).isZero)
  letI : Subsingleton (F.H' 1 (U ⊓ V)) := by
    rw [h.inf_eq_bot]
    let _ : Subsingleton (⊥ : X.Opens).toScheme :=
      ⟨fun x _ ↦ False.elim x.property⟩
    exact (structureCohomologyOpenAddEquiv X ⊥ 1).toEquiv.subsingleton_congr.mpr
      (Modules.subsingleton_H_of_subsingleton
        (structureModule (⊥ : X.Opens).toScheme) 0)
  letI : Subsingleton (F.H' 0 S.X₁) := by
    change Subsingleton (F.H' 0 (U ⊓ V))
    infer_instance
  letI : Subsingleton (F.H' 1 S.X₁) := by
    change Subsingleton (F.H' 1 (U ⊓ V))
    infer_instance
  letI : Module k (F.H' 1 S.X₄) :=
    Abelian.Ext.moduleOfRingHom phi 1
  letI : Module k (F.H' 1 S.X₂) :=
    Abelian.Ext.moduleOfRingHom phi 1
  letI : Module k (F.H' 1 S.X₃) :=
    Abelian.Ext.moduleOfRingHom phi 1
  exact eT.trans
    ((S.HOneLinearEquivBiprodOfIntersectionVanishing F phi).trans
        ((structureCohomologyOpenLinearEquiv k X U 1).prodCongr
          (structureCohomologyOpenLinearEquiv k X V 1)))

/-- First structure-sheaf cohomology of a binary coproduct is the product of the
cohomologies of its summands, as additive groups. -/
noncomputable def structureCohomologyCoprodAddEquiv
    (X Y : Scheme.{u}) :
    Modules.H (structureModule (X ⨿ Y)) 1 ≃+
      (Modules.H (structureModule X) 1 ×
        Modules.H (structureModule Y) 1) :=
  (structureCohomologyComplOpenAddEquiv (X ⨿ Y)
      (coprod.inl (C := Scheme)).opensRange
      (coprod.inr (C := Scheme)).opensRange
      (isCompl_opensRange_inl_inr X Y)).trans
    ((structureCohomologyAddEquivOfIso
      (coprod.inl (C := Scheme)).isoOpensRange 1).symm.prodCongr
        (structureCohomologyAddEquivOfIso
          (coprod.inr (C := Scheme)).isoOpensRange 1).symm)

/-- The structure morphism on a binary coproduct of schemes over a ring. -/
noncomputable def coprodStructureMap
    (k : Type u) [CommRing k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] :
    X ⨿ Y ⟶ Spec (CommRingCat.of k) :=
  coprod.desc (X ↘ Spec (CommRingCat.of k))
    (Y ↘ Spec (CommRingCat.of k))

/-- The canonical scheme-over-a-ring instance on a binary coproduct. -/
@[instance_reducible]
noncomputable def coprodOver
    (k : Type u) [CommRing k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] :
    (X ⨿ Y).Over (Spec (CommRingCat.of k)) :=
  ⟨coprodStructureMap k X Y⟩

/-- The canonical isomorphism from the left summand to its open range, over the base. -/
noncomputable def inlIsoOpensRangeOver
    (k : Type u) [CommRing k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] :
    Over.mk (X ↘ Spec (CommRingCat.of k)) ≅
      Over.mk ((coprod.inl (C := Scheme)).opensRange.ι ≫
        coprodStructureMap k X Y) := by
  refine Over.isoMk (coprod.inl (C := Scheme)).isoOpensRange ?_
  change (coprod.inl (C := Scheme)).isoOpensRange.hom ≫
    ((coprod.inl (C := Scheme)).opensRange.ι ≫
      coprodStructureMap k X Y) = X ↘ Spec (CommRingCat.of k)
  rw [← Category.assoc, AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι]
  exact coprod.inl_desc _ _

/-- The canonical isomorphism from the right summand to its open range, over the base. -/
noncomputable def inrIsoOpensRangeOver
    (k : Type u) [CommRing k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] :
    Over.mk (Y ↘ Spec (CommRingCat.of k)) ≅
      Over.mk ((coprod.inr (C := Scheme)).opensRange.ι ≫
        coprodStructureMap k X Y) := by
  refine Over.isoMk (coprod.inr (C := Scheme)).isoOpensRange ?_
  change (coprod.inr (C := Scheme)).isoOpensRange.hom ≫
    ((coprod.inr (C := Scheme)).opensRange.ι ≫
      coprodStructureMap k X Y) = Y ↘ Spec (CommRingCat.of k)
  rw [← Category.assoc, AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι]
  exact coprod.inr_desc _ _

/-- First structure-sheaf cohomology of a binary coproduct is the product of the
cohomologies of its summands, linearly over the base field. -/
noncomputable def structureCohomologyCoprodLinearEquiv
    (k : Type u) [Field k] (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))]
    [Y.Over (Spec (CommRingCat.of k))] :
    letI := coprodOver k X Y
    Modules.H (structureModule (X ⨿ Y)) 1 ≃ₗ[k]
      (Modules.H (structureModule X) 1 ×
        Modules.H (structureModule Y) 1) := by
  letI := coprodOver k X Y
  exact (structureCohomologyComplOpenLinearEquiv k (X ⨿ Y)
      (coprod.inl (C := Scheme)).opensRange
      (coprod.inr (C := Scheme)).opensRange
      (isCompl_opensRange_inl_inr X Y)).trans
    ((structureCohomologyLinearEquivOfOverIso k
      (inlIsoOpensRangeOver k X Y) 1).symm.prodCongr
        (structureCohomologyLinearEquivOfOverIso k
          (inrIsoOpensRangeOver k X Y) 1).symm)

/-- Reindexing a scheme coproduct along an equivalence gives an isomorphism over the
common base. -/
noncomputable def sigmaReindexOverIso
    (k : Type u) [CommRing k] {alpha beta : Type u}
    (e : alpha ≃ beta) (X : beta → Scheme.{u})
    [∀ i, (X i).Over (Spec (CommRingCat.of k))] :
    letI : ∀ i, ((X ∘ e) i).Over (Spec (CommRingCat.of k)) :=
      fun i ↦ (inferInstance : (X (e i)).Over (Spec (CommRingCat.of k)))
    letI := sigmaOver (fun a ↦ X (e a)) k
    letI := sigmaOver X k
    (∐ fun a ↦ X (e a)).asOver (Spec (CommRingCat.of k)) ≅
      (∐ X).asOver (Spec (CommRingCat.of k)) := by
  letI : ∀ i, ((X ∘ e) i).Over (Spec (CommRingCat.of k)) :=
    fun i ↦ (inferInstance : (X (e i)).Over (Spec (CommRingCat.of k)))
  letI := sigmaOver (fun a ↦ X (e a)) k
  letI := sigmaOver X k
  refine Over.isoMk (Limits.Sigma.reindex e X) ?_
  apply Limits.Sigma.hom_ext
  intro a
  change Limits.Sigma.ι (X ∘ e) a ≫
      (Limits.Sigma.reindex e X).hom ≫ sigmaStructureMap X k =
    Limits.Sigma.ι (X ∘ e) a ≫
      sigmaStructureMap (X ∘ e) k
  rw [← Category.assoc, Limits.Sigma.ι_reindex_hom,
    sigmaι_sigmaStructureMap, sigmaι_sigmaStructureMap]
  rfl

/-- The coproduct indexed by `Option alpha` as the coproduct of its `some` summands and
its `none` summand.  This variant supports the finite-coproduct cohomology induction. -/
noncomputable def sigmaOptionIsoForCohomology
    {alpha : Type u} (X : Option alpha → Scheme.{u}) :
    (∐ fun a : alpha ↦ X (some a)) ⨿ X none ≅ ∐ X where
  hom := coprod.desc
    (Limits.Sigma.desc fun a ↦ Limits.Sigma.ι X (some a))
    (Limits.Sigma.ι X none)
  inv := Limits.Sigma.desc fun o ↦ match o with
    | none => coprod.inr
    | some a => Limits.Sigma.ι (fun a : alpha ↦ X (some a)) a ≫ coprod.inl
  hom_inv_id := by
    apply coprod.hom_ext
    · apply Limits.Sigma.hom_ext
      intro a
      simp
    · simp
  inv_hom_id := by
    apply Limits.Sigma.hom_ext
    intro o
    cases o <;> simp

/-- The left coproduct inclusion followed by `sigmaOptionIsoForCohomology` is the
coproduct map of the `some` inclusions. -/
@[reassoc (attr := simp)]
lemma sigmaOptionIsoForCohomology_inl_hom
    {alpha : Type u} (X : Option alpha → Scheme.{u}) :
    coprod.inl ≫ (sigmaOptionIsoForCohomology X).hom =
      Limits.Sigma.desc (fun a ↦ Limits.Sigma.ι X (some a)) := by
  simp [sigmaOptionIsoForCohomology]

/-- The right coproduct inclusion followed by `sigmaOptionIsoForCohomology` is the
`none` inclusion. -/
@[reassoc (attr := simp)]
lemma sigmaOptionIsoForCohomology_inr_hom
    {alpha : Type u} (X : Option alpha → Scheme.{u}) :
    coprod.inr ≫ (sigmaOptionIsoForCohomology X).hom =
      Limits.Sigma.ι X none := by
  simp [sigmaOptionIsoForCohomology]

/-- Splitting an `Option`-indexed scheme coproduct into the `some` and `none` summands
gives an isomorphism over the common base. -/
noncomputable def sigmaOptionOverIso
    (k : Type u) [CommRing k] {alpha : Type u}
    (X : Option alpha → Scheme.{u})
    [∀ i, (X i).Over (Spec (CommRingCat.of k))] :
    letI := sigmaOver (fun a : alpha ↦ X (some a)) k
    letI := coprodOver k (∐ fun a : alpha ↦ X (some a)) (X none)
    letI := sigmaOver X k
    ((∐ fun a : alpha ↦ X (some a)) ⨿ X none).asOver
        (Spec (CommRingCat.of k)) ≅
      (∐ X).asOver (Spec (CommRingCat.of k)) := by
  letI := sigmaOver (fun a : alpha ↦ X (some a)) k
  letI := coprodOver k (∐ fun a : alpha ↦ X (some a)) (X none)
  letI := sigmaOver X k
  refine Over.isoMk (sigmaOptionIsoForCohomology X) ?_
  apply coprod.hom_ext
  · change coprod.inl ≫ (sigmaOptionIsoForCohomology X).hom ≫
        sigmaStructureMap X k =
      coprod.inl ≫ coprodStructureMap k
        (∐ fun a : alpha ↦ X (some a)) (X none)
    rw [← Category.assoc, sigmaOptionIsoForCohomology_inl_hom]
    apply Limits.Sigma.hom_ext
    intro a
    rw [← Category.assoc, Limits.Sigma.ι_desc,
      sigmaι_sigmaStructureMap]
    dsimp only [coprodStructureMap]
    rw [coprod.inl_desc]
    exact (sigmaι_sigmaStructureMap
      (fun a : alpha ↦ X (some a)) k a).symm
  · change coprod.inr ≫ (sigmaOptionIsoForCohomology X).hom ≫
        sigmaStructureMap X k =
      coprod.inr ≫ coprodStructureMap k
        (∐ fun a : alpha ↦ X (some a)) (X none)
    rw [← Category.assoc, sigmaOptionIsoForCohomology_inr_hom,
      sigmaι_sigmaStructureMap]
    exact (coprod.inr_desc _ _).symm

/-- A finite coproduct's first structure-sheaf cohomology is linearly equivalent to
the dependent product of the summands' first cohomology spaces. -/
theorem nonempty_structureCohomologySigmaOneLinearEquiv
    (k : Type u) [Field k] (iota : Type u) [Finite iota]
    (X : iota → Scheme.{u})
    [∀ i, (X i).Over (Spec (CommRingCat.of k))] :
    letI := sigmaOver X k
    Nonempty (Modules.H (structureModule (∐ X)) 1 ≃ₗ[k]
      (∀ i, Modules.H (structureModule (X i)) 1)) := by
  letI := Fintype.ofFinite iota
  let P : (iota : Type u) → [Fintype iota] → Prop := fun iota _ ↦
    ∀ (X : iota → Scheme.{u})
      (hX : ∀ i, (X i).Over (Spec (CommRingCat.of k))),
      letI : ∀ i, (X i).Over (Spec (CommRingCat.of k)) := hX
      letI := sigmaOver X k
      Nonempty (Modules.H (structureModule (∐ X)) 1 ≃ₗ[k]
        (∀ i, Modules.H (structureModule (X i)) 1))
  have hP : P iota := Fintype.induction_empty_option (P := P)
    (fun alpha beta _ e hAlpha X hX ↦ by
      letI : ∀ i, (X i).Over (Spec (CommRingCat.of k)) := hX
      let hComp : ∀ i, ((X ∘ e) i).Over (Spec (CommRingCat.of k)) :=
        fun i ↦ hX (e i)
      letI : ∀ i, ((X ∘ e) i).Over (Spec (CommRingCat.of k)) := hComp
      letI := sigmaOver (X ∘ e) k
      letI := sigmaOver X k
      obtain ⟨ih⟩ := hAlpha (X ∘ e) hComp
      exact ⟨((structureCohomologyLinearEquivOfOverIso k
        (sigmaReindexOverIso k e X) 1).symm.trans ih).trans
          (LinearEquiv.piCongrLeft k
            (fun i ↦ Modules.H (structureModule (X i)) 1) e)⟩)
    (by
      intro X hX
      letI : ∀ i, (X i).Over (Spec (CommRingCat.of k)) := hX
      letI := sigmaOver X k
      let _ : IsEmpty (∐ X : Scheme.{u}) :=
        ⟨fun x ↦ ((sigmaMk X).symm x).1.elim⟩
      let _ : Subsingleton (∐ X : Scheme.{u}) := inferInstance
      letI : Subsingleton (Modules.H (structureModule (∐ X)) 1) :=
        Modules.subsingleton_H_of_subsingleton (structureModule (∐ X)) 0
      letI : Subsingleton
          (∀ i, Modules.H (structureModule (X i)) 1) :=
        ⟨fun f g ↦ funext fun i ↦ i.elim⟩
      exact ⟨LinearEquiv.ofSubsingleton _ _⟩)
    (fun alpha _ hAlpha X hX ↦ by
      letI : ∀ i, (X i).Over (Spec (CommRingCat.of k)) := hX
      let XSome := fun a : alpha ↦ X (some a)
      let hSome : ∀ a, (XSome a).Over (Spec (CommRingCat.of k)) :=
        fun a ↦ hX (some a)
      letI : ∀ a, (XSome a).Over (Spec (CommRingCat.of k)) := hSome
      letI := sigmaOver XSome k
      letI := coprodOver k (∐ XSome) (X none)
      letI := sigmaOver X k
      obtain ⟨ih⟩ := hAlpha XSome hSome
      let eIso := structureCohomologyLinearEquivOfOverIso k
        (sigmaOptionOverIso k X) 1
      let eCoprod := structureCohomologyCoprodLinearEquiv k
        (∐ XSome) (X none)
      let ePi :
          (Modules.H (structureModule (X none)) 1 ×
              (∀ i : alpha, Modules.H (structureModule (X (some i))) 1)) ≃ₗ[k]
            (∀ i, Modules.H (structureModule (X i)) 1) :=
        (LinearEquiv.piOptionEquivProd (ι := alpha)
          (M := fun i ↦ Modules.H (structureModule (X i)) 1) k).symm
      exact ⟨(((eIso.symm.trans eCoprod).trans
        (ih.prodCongr (LinearEquiv.refl k _))).trans
          (LinearEquiv.prodComm k _ _)).trans ePi⟩)
    iota
  exact hP X (fun i ↦ inferInstance)

/-- Chosen linear equivalence between first structure-sheaf cohomology of a finite
coproduct and the dependent product of the summands' first cohomology spaces. -/
noncomputable def structureCohomologySigmaOneLinearEquiv
    (k : Type u) [Field k] {iota : Type u} [Finite iota]
    (X : iota → Scheme.{u})
    [∀ i, (X i).Over (Spec (CommRingCat.of k))] :
    letI := sigmaOver X k
    Modules.H (structureModule (∐ X)) 1 ≃ₗ[k]
      (∀ i, Modules.H (structureModule (X i)) 1) :=
  Classical.choice (nonempty_structureCohomologySigmaOneLinearEquiv k iota X)

/-- A finite coproduct has finite-dimensional first structure-sheaf cohomology when
each summand does. -/
noncomputable instance finiteDimensional_structureCohomologySigmaOne
    (k : Type u) [Field k] {iota : Type u} [Finite iota]
    (X : iota → Scheme.{u})
    [∀ i, (X i).Over (Spec (CommRingCat.of k))]
    [∀ i, FiniteDimensional k
      (Modules.H (structureModule (X i)) 1)] :
    letI := sigmaOver X k
    FiniteDimensional k (Modules.H (structureModule (∐ X)) 1) := by
  letI := sigmaOver X k
  exact Module.Finite.equiv
    (structureCohomologySigmaOneLinearEquiv k X).symm

/-- The first structure-sheaf cohomology dimension of a finite coproduct is the sum
of the corresponding dimensions of its summands. -/
theorem Modules.h_structureModule_sigma_one_eq_sum
    (k : Type u) [Field k] {iota : Type u} [Fintype iota]
    (X : iota → Scheme.{u})
    [∀ i, (X i).Over (Spec (CommRingCat.of k))]
    [∀ i, FiniteDimensional k
      (Modules.H (structureModule (X i)) 1)] :
    letI := sigmaOver X k
    Modules.h k (structureModule (∐ X)) 1 =
      ∑ i, Modules.h k (structureModule (X i)) 1 := by
  letI := sigmaOver X k
  let _ := finiteDimensional_structureCohomologySigmaOne k X
  letI : ∀ i, Module.Free k
      (Modules.H (structureModule (X i)) 1) := fun i ↦ inferInstance
  letI : ∀ i, Module.Finite k
      (Modules.H (structureModule (X i)) 1) := fun i ↦ inferInstance
  exact (structureCohomologySigmaOneLinearEquiv k X).finrank_eq.trans
    (Module.finrank_pi_fintype k)

end AlgebraicGeometry.Scheme

end
