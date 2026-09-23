module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksAndModuli.API.ExteriorPowerSheaf
public import StacksAndModuli.API.SheafifyComparison

/-!
# The exterior power of a sheaf of modules on a scheme

Supporting API with no Stacks Project counterpart of its own, consumed by the relative
Plücker embedding `Gr(q, V) ↪ Gr(1, ⋀^q V)` of **Theorem 2.1.1**: for a sheaf of modules
`M` on a scheme `X`, the sheafification `⋀^n M` of the presheaf `U ↦ ⋀[O(U)]^n M(U)`.

Main declarations:
- `AlgebraicGeometry.Scheme.Modules.exteriorPowerPresheaf`;
- `AlgebraicGeometry.Scheme.Modules.exteriorPower`;
- `AlgebraicGeometry.Scheme.Modules.toExteriorPower` (the sheafification unit).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
set_option linter.style.haveILetI false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The exterior-power presheaf of a sheaf of modules on a scheme:
`U ↦ ⋀[O(U)]^n M(U)`. -/
noncomputable def exteriorPowerPresheaf (M : X.Modules) (n : ℕ) :
    X.PresheafOfModules :=
  _root_.PresheafOfModules.exteriorPower (R := X.sheaf.val)
    (M := (M.val :
      _root_.PresheafOfModules.{u} (X.sheaf.val ⋙ forget₂ CommRingCat RingCat))) n

/-- **The exterior power of a sheaf of modules on a scheme**: the sheafification of the
exterior-power presheaf. -/
noncomputable def exteriorPower (M : X.Modules) (n : ℕ) : X.Modules :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj
    (exteriorPowerPresheaf M n)

/-- The sheafification unit of the exterior power: the canonical morphism from the
exterior-power presheaf to (the restriction of scalars along the identity of) the
exterior-power sheaf. -/
noncomputable def toExteriorPower (M : X.Modules) (n : ℕ) :
    exteriorPowerPresheaf M n ⟶
      (_root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.val)).obj
        (exteriorPower M n).val :=
  _root_.PresheafOfModules.toSheafify (𝟙 X.ringCatSheaf.val)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      (exteriorPowerPresheaf M n).presheaf)

/-- Functoriality of the exterior-power sheaf. -/
noncomputable def exteriorPowerMap {M N : X.Modules} (φ : M ⟶ N) (n : ℕ) :
    exteriorPower M n ⟶ exteriorPower N n :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map
    (_root_.PresheafOfModules.exteriorPowerMap n
      (show (M.val : _root_.PresheafOfModules.{u}
          (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) ⟶
        (N.val : _root_.PresheafOfModules.{u}
          (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) from
        (SheafOfModules.forget _).map φ))

/-- The exterior-power sheaf of an isomorphism of sheaves of modules. -/
noncomputable def exteriorPowerIso {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    exteriorPower M n ≅ exteriorPower N n :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).mapIso
    (_root_.PresheafOfModules.exteriorPowerMapIso n
      (show (M.val : _root_.PresheafOfModules.{u}
          (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) ≅
        (N.val : _root_.PresheafOfModules.{u}
          (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) from
        (SheafOfModules.forget _).mapIso e))

instance (M : X.Modules) (n : ℕ) :
    _root_.PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      (toExteriorPower M n) :=
  inferInstanceAs (_root_.PresheafOfModules.IsLocallySurjective _
    (_root_.PresheafOfModules.toSheafify _ _))

instance (M : X.Modules) (n : ℕ) :
    _root_.PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      (toExteriorPower M n) :=
  inferInstanceAs (_root_.PresheafOfModules.IsLocallyInjective _
    (_root_.PresheafOfModules.toSheafify _ _))


/-- Functoriality of the exterior-power sheaf: identities. -/
lemma exteriorPowerMap_id (M : X.Modules) (n : ℕ) :
    exteriorPowerMap (𝟙 M) n = 𝟙 (exteriorPower M n) := by
  rw [exteriorPowerMap]
  rw [show (show (M.val : _root_.PresheafOfModules.{u}
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) ⟶
    (M.val : _root_.PresheafOfModules.{u}
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) from
    (SheafOfModules.forget _).map (𝟙 M)) = 𝟙 _ from
      (SheafOfModules.forget X.ringCatSheaf).map_id M]
  rw [_root_.PresheafOfModules.exteriorPowerMap_id]
  exact CategoryTheory.Functor.map_id _ _

/-- Functoriality of the exterior-power sheaf: composition. -/
lemma exteriorPowerMap_comp {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (n : ℕ) :
    exteriorPowerMap (φ ≫ ψ) n = exteriorPowerMap φ n ≫ exteriorPowerMap ψ n := by
  rw [exteriorPowerMap, exteriorPowerMap, exteriorPowerMap, ← Functor.map_comp]
  refine congrArg (fun k ↦
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).map k) ?_
  rw [show (show (M.val : _root_.PresheafOfModules.{u}
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) ⟶
    (K.val : _root_.PresheafOfModules.{u}
      (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) from
    (SheafOfModules.forget _).map (φ ≫ ψ)) =
      (SheafOfModules.forget _).map φ ≫ (SheafOfModules.forget _).map ψ from
    (SheafOfModules.forget X.ringCatSheaf).map_comp φ ψ]
  exact _root_.PresheafOfModules.exteriorPowerMap_comp n _ _

@[simp]
lemma exteriorPowerIso_hom {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    (exteriorPowerIso e n).hom = exteriorPowerMap e.hom n := rfl

@[simp]
lemma exteriorPowerIso_inv {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    (exteriorPowerIso e n).inv = exteriorPowerMap e.inv n := rfl



set_option maxHeartbeats 1600000 in
-- the span induction and separatedness cross the sheafification spellings
/-- **Extensionality for morphisms out of an exterior-power sheaf**: two morphisms
agreeing on the sheafification units of all wedges are equal. -/
lemma exteriorPower_hom_ext {M Z : X.Modules} {q : ℕ}
    (a b : exteriorPower M q ⟶ Z)
    (h : ∀ (U : X.Opens) (m : Fin q → Γ(M, U)),
      (a.app U) (((toExteriorPower M q).app (Opposite.op U)).hom
          (_root_.exteriorPower.ιMulti Γ(X, U) q m)) =
        (b.app U) (((toExteriorPower M q).app (Opposite.op U)).hom
          (_root_.exteriorPower.ιMulti Γ(X, U) q m))) :
    a = b := by
  -- step 1: the two morphisms agree on units of arbitrary presheaf elements
  have hspan : ∀ (U : X.Opens)
      (w : (⋀[Γ(X, U)]^q Γ(M, U) :
        Submodule Γ(X, U) (ExteriorAlgebra Γ(X, U) Γ(M, U)))),
      (a.app U) (((toExteriorPower M q).app (Opposite.op U)).hom w) =
        (b.app U) (((toExteriorPower M q).app (Opposite.op U)).hom w) := by
    intro U w
    have hw : w ∈ Submodule.span Γ(X, U)
        (Set.range (_root_.exteriorPower.ιMulti Γ(X, U) q (M := Γ(M, U)))) := by
      rw [_root_.exteriorPower.ιMulti_span]
      trivial
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨m, rfl⟩ := hw
      exact h U m
    | zero => rw [map_zero, map_zero, map_zero]
    | add u v hu hv h1 h2 => rw [map_add, map_add, map_add, h1, h2]
    | smul r u hu h1 =>
      have hu1 : ((toExteriorPower M q).app (Opposite.op U)).hom (r • u) =
          r • ((toExteriorPower M q).app (Opposite.op U)).hom u :=
        ((toExteriorPower M q).app (Opposite.op U)).hom.map_smul r u
      rw [hu1, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, h1]
  -- step 2: sections are locally units, and the target sheaf is separated
  refine Scheme.Modules.hom_ext a b (fun U ↦ ?_)
  ext t
  refine (Scheme.Modules.isSheaf Z).section_ext (U := Opposite.op U) ?_
  intro x hx
  obtain ⟨W, g, hg, hxW⟩ := Presheaf.imageSieve_mem (Opens.grothendieckTopology ↥X)
    ((_root_.PresheafOfModules.toPresheaf _).map (toExteriorPower M q))
    (U := Opposite.op U)
    (show ToType (((_root_.PresheafOfModules.toPresheaf _).obj
      ((_root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.val)).obj
        (exteriorPower M q).val)).obj (Opposite.op U)) from t) x hx
  obtain ⟨w, hw⟩ := hg
  refine ⟨W, leOfHom g, hxW, ?_⟩
  have hres : ∀ (c : exteriorPower M q ⟶ Z),
      (Scheme.Modules.presheaf Z).map (homOfLE (leOfHom g)).op ((c.app U) t) =
        (c.app W) (((toExteriorPower M q).app (Opposite.op W)).hom w) := by
    intro c
    have hnat := _root_.PresheafOfModules.naturality_apply
      ((SheafOfModules.forget _).map c) (homOfLE (leOfHom g)).op t
    refine hnat.symm.trans ?_
    exact congrArg (fun y ↦ (c.app W) y) hw.symm
  rw [hres a, hres b, hspan W w]


/-- The action of the exterior-power functoriality on the unit of a wedge. -/
lemma exteriorPowerMap_app_unit_ιMulti {M N : X.Modules} (ψ : M ⟶ N) (q : ℕ)
    (U : X.Opens) (m : Fin q → Γ(M, U)) :
    ((exteriorPowerMap ψ q).app U)
        (((toExteriorPower M q).app (Opposite.op U)).hom
          (_root_.exteriorPower.ιMulti Γ(X, U) q m)) =
      ((toExteriorPower N q).app (Opposite.op U)).hom
        (_root_.exteriorPower.ιMulti Γ(X, U) q
          (fun i ↦ show Γ(N, U) from ψ.app U (m i))) := by
  have hnat := CategoryTheory.congr_fun (NatTrans.congr_app
    (CategoryTheory.toSheafify_naturality
      (J := Opens.grothendieckTopology ↥X)
      ((_root_.PresheafOfModules.toPresheaf _).map
        (_root_.PresheafOfModules.exteriorPowerMap (R := X.sheaf.val) q
          (show (M.val : _root_.PresheafOfModules.{u}
              (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) ⟶
            (N.val : _root_.PresheafOfModules.{u}
              (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) from
            (SheafOfModules.forget _).map ψ)))) (Opposite.op U))
    (_root_.exteriorPower.ιMulti Γ(X, U) q m)
  refine Eq.trans hnat.symm ?_
  refine congrArg (ConcreteCategory.hom
    ((toExteriorPower N q).app (Opposite.op U))) ?_
  exact _root_.PresheafOfModules.exteriorPowerMapApp_ιMulti q
    (show (M.val : _root_.PresheafOfModules.{u}
        (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) ⟶
      (N.val : _root_.PresheafOfModules.{u}
        (X.sheaf.val ⋙ forget₂ CommRingCat RingCat)) from
      (SheafOfModules.forget _).map ψ) (Opposite.op U) m


end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open AlgebraicGeometry.Scheme TopologicalSpace

variable {R : CommRingCat.{u}} (M₀ : ModuleCat.{u} R) (n : ℕ)

/-- The wedge of restrictions: the `R`-linear map from the exterior power of the module to
the exterior power of the sections of its tilde over an open. -/
noncomputable def wedgeToOpen (U : (Spec R).Opens) :
    (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)) →ₗ[R]
      (⋀[Γ(Spec R, U)]^n Γ(ModuleCat.tilde M₀, U) :
        Submodule Γ(Spec R, U) (ExteriorAlgebra Γ(Spec R, U) Γ(ModuleCat.tilde M₀, U))) :=
  haveI : IsScalarTower R Γ(Spec R, U) Γ(ModuleCat.tilde M₀, U) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦
      (Scheme.Modules.smul_Spec_def (M := ModuleCat.tilde M₀) r x).symm
  let t : M₀ →ₗ[R] Γ(ModuleCat.tilde M₀, U) := (tilde.toOpen M₀ U).hom
  exteriorPower.mapSemilinear R Γ(Spec R, U) n M₀ t

@[simp]
lemma wedgeToOpen_ιMulti (U : (Spec R).Opens) (m : Fin n → M₀) :
    wedgeToOpen M₀ n U (_root_.exteriorPower.ιMulti R n m) =
      _root_.exteriorPower.ιMulti Γ(Spec R, U) n
        (fun i ↦ show Γ(ModuleCat.tilde M₀, U) from tilde.toOpen M₀ U (m i)) := by
  haveI : IsScalarTower R Γ(Spec R, U) Γ(ModuleCat.tilde M₀, U) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦
      (Scheme.Modules.smul_Spec_def (M := ModuleCat.tilde M₀) r x).symm
  let t : M₀ →ₗ[R] Γ(ModuleCat.tilde M₀, U) := (tilde.toOpen M₀ U).hom
  exact exteriorPower.mapSemilinear_ιMulti R Γ(Spec R, U) n M₀ t m

/-- The wedge of restrictions commutes with the restriction maps of the exterior-power
presheaf. -/
lemma exteriorPowerPresheaf_map_wedgeToOpen {U V : (Spec R).Opens} (h : V ≤ U)
    (w : (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))) :
    ((Scheme.Modules.exteriorPowerPresheaf (ModuleCat.tilde M₀) n).map
        (homOfLE h).op).hom (wedgeToOpen M₀ n U w) =
      wedgeToOpen M₀ n V w := by
  haveI : IsScalarTower R Γ(Spec R, U) Γ(ModuleCat.tilde M₀, U) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦
      (Scheme.Modules.smul_Spec_def (M := ModuleCat.tilde M₀) r x).symm
  haveI : IsScalarTower R Γ(Spec R, V) Γ(ModuleCat.tilde M₀, V) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦
      (Scheme.Modules.smul_Spec_def (M := ModuleCat.tilde M₀) r x).symm
  have hw : w ∈ Submodule.span R
      (Set.range (_root_.exteriorPower.ιMulti R n (M := M₀))) := by
    rw [_root_.exteriorPower.ιMulti_span]
    trivial
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨m, rfl⟩ := hw
    rw [wedgeToOpen_ιMulti, wedgeToOpen_ιMulti]
    exact Eq.trans (_root_.PresheafOfModules.exteriorPowerObjMap_ιMulti
      (R := (Spec R).sheaf.val)
      (M := ((ModuleCat.tilde M₀).val : _root_.PresheafOfModules.{u}
        ((Spec R).sheaf.val ⋙ forget₂ CommRingCat RingCat))) n (homOfLE h).op
      (fun i ↦ tilde.toOpen M₀ U (m i))) rfl
  | zero =>
    simp
  | add u v hu hv h1 h2 =>
    rw [map_add, map_add, h1, h2, map_add]
  | smul r u hu h1 =>
    have hres : ((Spec R).presheaf.map (homOfLE h).op).hom (algebraMap R Γ(Spec R, U) r) =
        algebraMap R Γ(Spec R, V) r := by
      change ((Spec R).presheaf.map (homOfLE le_top).op ≫
        (Spec R).presheaf.map (homOfLE h).op).hom ((Scheme.ΓSpecIso R).inv.hom r) = _
      rw [← Functor.map_comp, ← op_comp]
      rfl
    have hres' : (ConcreteCategory.hom ((Spec R).ringCatSheaf.val.map (homOfLE h).op))
        (algebraMap R Γ(Spec R, U) r) = algebraMap R Γ(Spec R, V) r := hres
    rw [LinearMap.map_smul, LinearMap.map_smul,
      ← algebraMap_smul (R := R) Γ(Spec R, U) r (wedgeToOpen M₀ n U u),
      ← algebraMap_smul (R := R) Γ(Spec R, V) r (wedgeToOpen M₀ n V u),
      _root_.PresheafOfModules.map_smul, h1, hres']

/-- The exterior power of the tilde localizes on basic opens: over `D(f)`, the wedge of
restrictions exhibits the exterior power of the sections as the `f`-power localization of
the exterior power of the module. -/
theorem isLocalizedModule_wedgeToOpen (f : R) :
    haveI : IsScalarTower R Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens))
        Γ(tilde M₀, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) :=
      IsScalarTower.of_algebraMap_smul fun r x ↦
        (Scheme.Modules.smul_Spec_def (M := tilde M₀) r x).symm
    IsLocalizedModule (Submonoid.powers f)
      (wedgeToOpen M₀ n (PrimeSpectrum.basicOpen f : (Spec R).Opens)) := by
  haveI : IsScalarTower R Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens))
      Γ(tilde M₀, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦
      (Scheme.Modules.smul_Spec_def (M := tilde M₀) r x).symm
  let t : M₀ →ₗ[R] Γ(tilde M₀, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) :=
    (tilde.toOpen M₀ (PrimeSpectrum.basicOpen f)).hom
  haveI : IsLocalizedModule (Submonoid.powers f) t :=
    inferInstanceAs (IsLocalizedModule.Away f
      (tilde.toOpen M₀ (PrimeSpectrum.basicOpen f)).hom)
  exact exteriorPower.isLocalizedModule_mapSemilinear R
    Γ(Spec R, (PrimeSpectrum.basicOpen f : (Spec R).Opens)) n M₀ (Submonoid.powers f) t

/-- The global-sections component of the tilde comparison: the `R`-linear map from the
exterior power of the module into the global sections of the exterior-power sheaf of the
tilde, via the sheafification unit applied to the wedge of restrictions. -/
noncomputable def wedgeComparisonΓLinear :
    (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)) →ₗ[R]
      Γ(Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n, (⊤ : (Spec R).Opens)) where
  toFun w :=
    show Γ(Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n, (⊤ : (Spec R).Opens)) from
      ((Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n).app (.op ⊤)).hom
        (wedgeToOpen M₀ n ⊤ w)
  map_add' u v := by
    dsimp only
    rw [map_add, map_add]
  map_smul' r w := by
    dsimp only [RingHom.id_apply]
    rw [LinearMap.map_smul,
      ← algebraMap_smul (R := R) Γ(Spec R, (⊤ : (Spec R).Opens)) r
        (wedgeToOpen M₀ n ⊤ w),
      LinearMap.map_smul]
    exact algebraMap_smul (R := R) Γ(Spec R, (⊤ : (Spec R).Opens)) r
      (show Γ(Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n, (⊤ : (Spec R).Opens)) from
        ((Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n).app (.op ⊤)).hom
          (wedgeToOpen M₀ n ⊤ w))

/-- The global-sections comparison as a morphism in `ModuleCat R`. -/
noncomputable def wedgeComparisonΓ :
    ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)) ⟶
      ModuleCat.of R
        Γ(Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n, (⊤ : (Spec R).Opens)) :=
  ModuleCat.ofHom (wedgeComparisonΓLinear M₀ n)

/-- **The tilde comparison for exterior powers**: the canonical morphism from the tilde of
the exterior power to the exterior power of the tilde. -/
noncomputable def exteriorPowerTildeComparison :
    ModuleCat.tilde
        (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))) ⟶
      Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n :=
  tilde.map (wedgeComparisonΓ M₀ n) ≫ Scheme.Modules.fromTildeΓ _

/-- **The comparison sends localized generators to unit values**: over every open, the
tilde comparison intertwines `toOpen` for the exterior power of the module with the
sheafification unit applied to the wedge of restrictions. -/
lemma exteriorPowerTildeComparison_toOpen (U : (Spec R).Opens)
    (w : (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))) :
    ((modulesSpecToSheaf.map (exteriorPowerTildeComparison M₀ n)).1.app (.op U)).hom
        ((tilde.toOpen
          (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))) U).hom w) =
      ((Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n).app (.op U)).hom
        (wedgeToOpen M₀ n U w) := by
  have h1 := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp
    (tilde.toOpen_map_app (wedgeComparisonΓ M₀ n) U)) w
  have h2 := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp
    (Scheme.Modules.toOpen_fromTildeΓ_app
      (Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n) U))
    ((wedgeComparisonΓ M₀ n).hom w)
  have h3 : ((modulesSpecToSheaf.map (exteriorPowerTildeComparison M₀ n)).1.app (.op U)).hom
        ((tilde.toOpen
          (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))) U).hom w) =
      ((modulesSpecToSheaf.obj (Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n)).1.map
        (homOfLE le_top).op).hom ((wedgeComparisonΓ M₀ n).hom w) := by
    rw [exteriorPowerTildeComparison, Functor.map_comp]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    rw [ModuleCat.hom_comp] at h2
    rw [show ((modulesSpecToSheaf.map (tilde.map (wedgeComparisonΓ M₀ n)) ≫
        modulesSpecToSheaf.map (Scheme.Modules.fromTildeΓ
          (Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n))).hom.app
            (Opposite.op U)) =
      (modulesSpecToSheaf.map (tilde.map (wedgeComparisonΓ M₀ n))).hom.app
          (Opposite.op U) ≫
        (modulesSpecToSheaf.map (Scheme.Modules.fromTildeΓ
          (Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n))).hom.app
            (Opposite.op U) from rfl]
    rw [ModuleCat.hom_comp, LinearMap.comp_apply]
    exact Eq.trans (congrArg (ModuleCat.Hom.hom
      ((modulesSpecToSheaf.map (Scheme.Modules.fromTildeΓ
        (Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n))).hom.app
          (Opposite.op U))) h1) h2
  rw [h3]
  have h4 := _root_.PresheafOfModules.naturality_apply
    (Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n) (homOfLE (le_top (a := U))).op
    (wedgeToOpen M₀ n ⊤ w)
  have h5 := exteriorPowerPresheaf_map_wedgeToOpen M₀ n (le_top (a := U)) w
  rw [h5] at h4
  exact h4.symm

/-- The sheafification unit commutes with the `R`-scalar action on sections. -/
lemma toExteriorPower_app_smul (V : (Spec R).Opens) (r : R)
    (w : (⋀[Γ(Spec R, V)]^n Γ(ModuleCat.tilde M₀, V) :
      Submodule Γ(Spec R, V) (ExteriorAlgebra Γ(Spec R, V) Γ(ModuleCat.tilde M₀, V)))) :
    haveI : IsScalarTower R Γ(Spec R, V) Γ(ModuleCat.tilde M₀, V) :=
      IsScalarTower.of_algebraMap_smul fun r x ↦
        (Scheme.Modules.smul_Spec_def (M := ModuleCat.tilde M₀) r x).symm
    ((Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n).app (.op V)).hom (r • w) =
      r • (show Γ(Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n, V) from
        ((Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n).app (.op V)).hom w) := by
  haveI : IsScalarTower R Γ(Spec R, V) Γ(ModuleCat.tilde M₀, V) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦
      (Scheme.Modules.smul_Spec_def (M := ModuleCat.tilde M₀) r x).symm
  rw [← algebraMap_smul (R := R) Γ(Spec R, V) r w, LinearMap.map_smul]
  exact algebraMap_smul (R := R) Γ(Spec R, V) r
    (show Γ(Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n, V) from
      ((Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n).app (.op V)).hom w)

section EndUnits

variable {M : (Spec R).Modules} {U : (Spec R).Opens} {f : R}

/-- Cancellation of powers of `f` on sections over opens inside `D(f)`. -/
lemma pow_smul_left_cancel (h : U ≤ PrimeSpectrum.basicOpen f) (k : ℕ) {x y : Γ(M, U)}
    (hxy : (f ^ k : R) • x = (f ^ k : R) • y) : x = y := by
  have hu : IsUnit (algebraMap R (Module.End R Γ(M, U)) (f ^ k)) := by
    rw [map_pow]
    exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f h).pow k
  refine (Module.End.isUnit_iff _).mp hu |>.injective ?_
  rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply]
  exact hxy

/-- Divisibility by powers of `f` on sections over opens inside `D(f)`. -/
lemma exists_pow_smul_eq (h : U ≤ PrimeSpectrum.basicOpen f) (k : ℕ) (y : Γ(M, U)) :
    ∃ x : Γ(M, U), (f ^ k : R) • x = y := by
  have hu : IsUnit (algebraMap R (Module.End R Γ(M, U)) (f ^ k)) := by
    rw [map_pow]
    exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f h).pow k
  obtain ⟨x, hx⟩ := (Module.End.isUnit_iff _).mp hu |>.surjective y
  exact ⟨x, by rw [← Module.algebraMap_end_apply (R := R) (S := R), hx]⟩

end EndUnits

/-- **Local surjectivity of the tilde comparison**: every section of the exterior-power
sheaf is, on a basic open around every point, in the image of the comparison from the
tilde of the exterior power. -/
theorem isLocallySurjective_exteriorPowerTildeComparison :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology ↥(Spec R))
      ((_root_.PresheafOfModules.toPresheaf _).map
        ((SheafOfModules.forget _).map (exteriorPowerTildeComparison M₀ n))) := by
  constructor
  intro U t x hx
  -- the sheafification unit is locally surjective: find a presheaf preimage near `x`
  obtain ⟨V, fVU, hf, hxV⟩ := Presheaf.imageSieve_mem (Opens.grothendieckTopology ↥(Spec R))
    ((_root_.PresheafOfModules.toPresheaf _).map
      (Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n)) (U := Opposite.op U) t x hx
  obtain ⟨w₁, hw₁⟩ := hf
  -- shrink to a basic open around `x`
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hxg, hgV : PrimeSpectrum.basicOpen _ ≤ V⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxV V.2
  haveI : IsScalarTower R Γ(Spec R, (PrimeSpectrum.basicOpen g : (Spec R).Opens))
      Γ(ModuleCat.tilde M₀, (PrimeSpectrum.basicOpen g : (Spec R).Opens)) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦
      (Scheme.Modules.smul_Spec_def (M := ModuleCat.tilde M₀) r x).symm
  refine ⟨PrimeSpectrum.basicOpen g, homOfLE hgV ≫ fVU, ?_, hxg⟩
  -- restrict the preimage to the basic open
  set w₂ : (⋀[Γ(Spec R, (PrimeSpectrum.basicOpen g : (Spec R).Opens))]^n
      Γ(ModuleCat.tilde M₀, (PrimeSpectrum.basicOpen g : (Spec R).Opens)) :
        Submodule Γ(Spec R, (PrimeSpectrum.basicOpen g : (Spec R).Opens))
          (ExteriorAlgebra Γ(Spec R, (PrimeSpectrum.basicOpen g : (Spec R).Opens))
            Γ(ModuleCat.tilde M₀, (PrimeSpectrum.basicOpen g : (Spec R).Opens)))) :=
    ((Scheme.Modules.exteriorPowerPresheaf (ModuleCat.tilde M₀) n).map
      (homOfLE hgV).op).hom w₁ with hw₂def
  have hcomp : ((Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n).val.presheaf.map
        ((homOfLE hgV ≫ fVU).op)) t =
      ((Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n).val.presheaf.map
        ((homOfLE hgV).op))
        (((Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n).val.presheaf.map fVU.op) t) := by
    rw [show ((homOfLE hgV ≫ fVU).op) = fVU.op ≫ (homOfLE hgV).op from rfl,
      Functor.map_comp]
    rfl
  have hw₂ : ((Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n).app
      (Opposite.op (PrimeSpectrum.basicOpen g : (Spec R).Opens))).hom w₂ =
      ((Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n).val.presheaf.map
        ((homOfLE hgV ≫ fVU).op)) t := by
    have hnat := _root_.PresheafOfModules.naturality_apply
      (Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n) (homOfLE hgV).op w₁
    refine Eq.trans hnat (Eq.trans ?_ hcomp.symm)
    exact congrArg (ConcreteCategory.hom
      (((_root_.PresheafOfModules.restrictScalars (𝟙 (Spec R).ringCatSheaf.val)).obj
        (Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n).val).map
          (homOfLE hgV).op)) hw₁
  -- localize the presheaf preimage: a power of `g` moves it into the wedge image
  haveI := isLocalizedModule_wedgeToOpen M₀ n g
  obtain ⟨⟨w₀, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers g)
    (wedgeToOpen M₀ n (PrimeSpectrum.basicOpen g : (Spec R).Opens)) w₂
  obtain ⟨k, hk⟩ := s.2
  have hk' : (g ^ k : R) = (s : R) := hk
  have hs' : (g ^ k : R) • w₂ =
      wedgeToOpen M₀ n (PrimeSpectrum.basicOpen g : (Spec R).Opens) w₀ := by
    rw [← hs]
    show (g ^ k : R) • w₂ = (s : R) • w₂
    rw [hk']
  -- divide the localized generator by that power on the tilde side
  obtain ⟨z, hz⟩ := exists_pow_smul_eq
    (M := ModuleCat.tilde (ModuleCat.of R
      (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))
    (le_refl (PrimeSpectrum.basicOpen g : (Spec R).Opens)) k
    ((tilde.toOpen (ModuleCat.of R
      (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
        (PrimeSpectrum.basicOpen g)).hom w₀)
  refine ⟨z, ?_⟩
  -- the comparison sends `z` to the restriction of `t`, after cancelling `g ^ k`
  refine pow_smul_left_cancel (M := Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n)
    (le_refl (PrimeSpectrum.basicOpen g : (Spec R).Opens)) k ?_
  have hχsmul : ((exteriorPowerTildeComparison M₀ n).app
        (PrimeSpectrum.basicOpen g : (Spec R).Opens)) ((g ^ k : R) • z) =
      ((g ^ k : R) • ((exteriorPowerTildeComparison M₀ n).app
        (PrimeSpectrum.basicOpen g : (Spec R).Opens)) z :
        Γ(Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n,
          (PrimeSpectrum.basicOpen g : (Spec R).Opens))) := by
    rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.Hom.app_smul,
      ← Scheme.Modules.smul_Spec_def]
  have key : ((exteriorPowerTildeComparison M₀ n).app
        (PrimeSpectrum.basicOpen g : (Spec R).Opens)) ((g ^ k : R) • z) =
      ((g ^ k : R) •
        (show Γ(Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n,
            (PrimeSpectrum.basicOpen g : (Spec R).Opens)) from
          ((Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n).val.presheaf.map
            ((homOfLE hgV ≫ fVU).op)) t) :
        Γ(Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n,
          (PrimeSpectrum.basicOpen g : (Spec R).Opens))) := by
    rw [hz]
    refine Eq.trans (exteriorPowerTildeComparison_toOpen M₀ n
      (PrimeSpectrum.basicOpen g : (Spec R).Opens) w₀) ?_
    rw [← hs']
    refine Eq.trans (toExteriorPower_app_smul M₀ n
      (PrimeSpectrum.basicOpen g : (Spec R).Opens) (g ^ k) w₂) ?_
    rw [hw₂]
  exact hχsmul.symm.trans key

/-- The `toOpen` of the tilde of the exterior power is the `f`-power localization over a
basic open (the generic tilde instance restated for the bundled exterior power, where
instance search does not fire). -/
lemma isLocalizedModule_wedge_toOpen (g : R) :
    IsLocalizedModule (Submonoid.powers g)
      (tilde.toOpen (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
        (PrimeSpectrum.basicOpen g)).hom :=
  IsLocalizedModule.of_linearEquiv (.powers g)
    (StructureSheaf.toOpenₗ R
      (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
      (PrimeSpectrum.basicOpen g))
    ((tilde.modulesSpecToSheafIso
      (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))).app
        _).toLinearEquiv.symm

/-- **Local injectivity of the tilde comparison**: two sections of the tilde of the
exterior power with the same image agree on a basic open around every point. -/
theorem isLocallyInjective_exteriorPowerTildeComparison :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology ↥(Spec R))
      ((_root_.PresheafOfModules.toPresheaf _).map
        ((SheafOfModules.forget _).map (exteriorPowerTildeComparison M₀ n))) := by
  constructor
  intro U t t' h x hx
  -- shrink to a basic open around `x`
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hxg, hgU : PrimeSpectrum.basicOpen _ ≤ U.unop⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx U.unop.2
  have hgU' : (PrimeSpectrum.basicOpen g : (Spec R).Opens) ≤ U.unop := hgU
  -- clear denominators for the two restricted sections
  haveI : IsLocalizedModule (Submonoid.powers g)
      (tilde.toOpen (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
          (PrimeSpectrum.basicOpen g)).hom :=
    isLocalizedModule_wedge_toOpen M₀ n g
  set tg : Γ(ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))),
      (PrimeSpectrum.basicOpen g : (Spec R).Opens)) :=
    (Scheme.Modules.presheaf (ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))).map
      (homOfLE hgU').op t with htg
  set tg' : Γ(ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))),
      (PrimeSpectrum.basicOpen g : (Spec R).Opens)) :=
    (Scheme.Modules.presheaf (ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))).map
      (homOfLE hgU').op t' with htg'
  obtain ⟨⟨y, s⟩, hy⟩ := IsLocalizedModule.surj (Submonoid.powers g)
    (tilde.toOpen (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
        (PrimeSpectrum.basicOpen g)).hom tg
  obtain ⟨⟨y', s'⟩, hy'⟩ := IsLocalizedModule.surj (Submonoid.powers g)
    (tilde.toOpen (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
        (PrimeSpectrum.basicOpen g)).hom tg'
  obtain ⟨k, hk⟩ := s.2
  obtain ⟨l, hl⟩ := s'.2
  have hk' : (g ^ k : R) = (s : R) := hk
  have hl' : (g ^ l : R) = (s' : R) := hl
  have hys : (s : R) • tg = (tilde.toOpen (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
      (PrimeSpectrum.basicOpen g)).hom y := hy
  have hys' : (s' : R) • tg' = (tilde.toOpen (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
      (PrimeSpectrum.basicOpen g)).hom y' := hy'
  set z : (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)) := (g ^ l : R) • y with hz
  set z' : (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)) := (g ^ k : R) • y' with hz'
  have hmz : (g ^ (k + l) : R) • tg =
      (tilde.toOpen (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
        (PrimeSpectrum.basicOpen g)).hom z := by
    rw [hz, LinearMap.map_smul, ← hys, ← hk', ← mul_smul, ← pow_add, add_comm l k]
  have hmz' : (g ^ (k + l) : R) • tg' =
      (tilde.toOpen (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
        (PrimeSpectrum.basicOpen g)).hom z' := by
    rw [hz', LinearMap.map_smul, ← hys', ← hl', ← mul_smul, ← pow_add]
  -- the comparison agrees on the restricted sections
  have hrest : ((exteriorPowerTildeComparison M₀ n).app
        (PrimeSpectrum.basicOpen g : (Spec R).Opens)) tg =
      ((exteriorPowerTildeComparison M₀ n).app
        (PrimeSpectrum.basicOpen g : (Spec R).Opens)) tg' := by
    have h1 := _root_.PresheafOfModules.naturality_apply
      ((SheafOfModules.forget _).map (exteriorPowerTildeComparison M₀ n))
      (homOfLE hgU').op t
    have h2 := _root_.PresheafOfModules.naturality_apply
      ((SheafOfModules.forget _).map (exteriorPowerTildeComparison M₀ n))
      (homOfLE hgU').op t'
    refine h1.trans (Eq.trans ?_ h2.symm)
    exact congrArg (ConcreteCategory.hom
      (((SheafOfModules.forget (Spec R).ringCatSheaf).obj
        (Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n)).map (homOfLE hgU').op)) h
  -- hence it agrees on the two `toOpen` images
  have hsm : ∀ (w : Γ(ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))),
      (PrimeSpectrum.basicOpen g : (Spec R).Opens))),
      ((exteriorPowerTildeComparison M₀ n).app
        (PrimeSpectrum.basicOpen g : (Spec R).Opens)) ((g ^ (k + l) : R) • w) =
      ((g ^ (k + l) : R) • ((exteriorPowerTildeComparison M₀ n).app
        (PrimeSpectrum.basicOpen g : (Spec R).Opens)) w :
        Γ(Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n,
          (PrimeSpectrum.basicOpen g : (Spec R).Opens))) := by
    intro w
    rw [Scheme.Modules.smul_Spec_def, Scheme.Modules.Hom.app_smul,
      ← Scheme.Modules.smul_Spec_def]
  have hχz : ((exteriorPowerTildeComparison M₀ n).app
        (PrimeSpectrum.basicOpen g : (Spec R).Opens))
        ((tilde.toOpen (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
            (PrimeSpectrum.basicOpen g)).hom z) =
      ((exteriorPowerTildeComparison M₀ n).app
        (PrimeSpectrum.basicOpen g : (Spec R).Opens))
        ((tilde.toOpen (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
            (PrimeSpectrum.basicOpen g)).hom z') := by
    rw [← hmz, ← hmz', hsm, hsm, hrest]
  -- transfer to the sheafification unit via the toOpen computation
  have hunit_eq : (ConcreteCategory.hom
        (((_root_.PresheafOfModules.toPresheaf _).map
          (Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n)).app
            (Opposite.op (PrimeSpectrum.basicOpen g : (Spec R).Opens))))
        (wedgeToOpen M₀ n (PrimeSpectrum.basicOpen g : (Spec R).Opens) z) =
      (ConcreteCategory.hom
        (((_root_.PresheafOfModules.toPresheaf _).map
          (Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n)).app
            (Opposite.op (PrimeSpectrum.basicOpen g : (Spec R).Opens))))
        (wedgeToOpen M₀ n (PrimeSpectrum.basicOpen g : (Spec R).Opens) z') := by
    have e1 := exteriorPowerTildeComparison_toOpen M₀ n
      (PrimeSpectrum.basicOpen g : (Spec R).Opens) z
    have e2 := exteriorPowerTildeComparison_toOpen M₀ n
      (PrimeSpectrum.basicOpen g : (Spec R).Opens) z'
    exact e1.symm.trans (hχz.trans e2)
  -- the unit is locally injective: the wedges agree on a cover
  have hsieve := Presheaf.IsLocallyInjective.equalizerSieve_mem
    (J := Opens.grothendieckTopology ↥(Spec R))
    (φ := (_root_.PresheafOfModules.toPresheaf _).map
      (Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n))
    (X := Opposite.op (PrimeSpectrum.basicOpen g : (Spec R).Opens))
    (show ToType (((_root_.PresheafOfModules.toPresheaf _).obj
        (Scheme.Modules.exteriorPowerPresheaf (ModuleCat.tilde M₀) n)).obj
          (Opposite.op (PrimeSpectrum.basicOpen g : (Spec R).Opens))) from
      wedgeToOpen M₀ n (PrimeSpectrum.basicOpen g : (Spec R).Opens) z)
    (show ToType (((_root_.PresheafOfModules.toPresheaf _).obj
        (Scheme.Modules.exteriorPowerPresheaf (ModuleCat.tilde M₀) n)).obj
          (Opposite.op (PrimeSpectrum.basicOpen g : (Spec R).Opens))) from
      wedgeToOpen M₀ n (PrimeSpectrum.basicOpen g : (Spec R).Opens) z') hunit_eq
  obtain ⟨W, fW, hfW, hxW⟩ := hsieve x hxg
  -- shrink again to a basic open
  obtain ⟨_, ⟨_, ⟨e, rfl⟩, rfl⟩, hxe, heW : PrimeSpectrum.basicOpen _ ≤ W⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxW W.2
  have heW' : (PrimeSpectrum.basicOpen e : (Spec R).Opens) ≤ W := heW
  have heg : (PrimeSpectrum.basicOpen e : (Spec R).Opens) ≤
      (PrimeSpectrum.basicOpen g : (Spec R).Opens) := heW'.trans (leOfHom fW)
  have heU : (PrimeSpectrum.basicOpen e : (Spec R).Opens) ≤ U.unop := heg.trans hgU'
  -- restrict the wedge equality to that basic open and cancel denominators
  have hDh2 : wedgeToOpen M₀ n (PrimeSpectrum.basicOpen e : (Spec R).Opens) z =
      wedgeToOpen M₀ n (PrimeSpectrum.basicOpen e : (Spec R).Opens) z' := by
    have hstep := congrArg (ConcreteCategory.hom
      (((_root_.PresheafOfModules.toPresheaf _).obj
        (Scheme.Modules.exteriorPowerPresheaf (ModuleCat.tilde M₀) n)).map
          (homOfLE heW').op)) hfW
    have hsplit : ∀ (a : ToType (((_root_.PresheafOfModules.toPresheaf _).obj
        (Scheme.Modules.exteriorPowerPresheaf (ModuleCat.tilde M₀) n)).obj
          (Opposite.op (PrimeSpectrum.basicOpen g : (Spec R).Opens)))),
        (ConcreteCategory.hom
          (((_root_.PresheafOfModules.toPresheaf _).obj
            (Scheme.Modules.exteriorPowerPresheaf (ModuleCat.tilde M₀) n)).map
              (homOfLE heg).op)) a =
        (ConcreteCategory.hom
          (((_root_.PresheafOfModules.toPresheaf _).obj
            (Scheme.Modules.exteriorPowerPresheaf (ModuleCat.tilde M₀) n)).map
              (homOfLE heW').op))
          ((ConcreteCategory.hom
            (((_root_.PresheafOfModules.toPresheaf _).obj
              (Scheme.Modules.exteriorPowerPresheaf (ModuleCat.tilde M₀) n)).map
                fW.op)) a) := by
      intro a
      rw [show (homOfLE heg) = homOfLE heW' ≫ fW from rfl, op_comp, Functor.map_comp]
      rfl
    have hzn := exteriorPowerPresheaf_map_wedgeToOpen M₀ n heg z
    have hzn' := exteriorPowerPresheaf_map_wedgeToOpen M₀ n heg z'
    exact hzn.symm.trans ((hsplit _).trans (hstep.trans ((hsplit _).symm.trans hzn')))
  haveI := isLocalizedModule_wedgeToOpen M₀ n e
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq
    (S := Submonoid.powers e)
    (f := wedgeToOpen M₀ n (PrimeSpectrum.basicOpen e : (Spec R).Opens)) hDh2
  obtain ⟨p, hp⟩ := c.2
  have hp' : (e ^ p : R) = (c : R) := hp
  have hc' : (e ^ p : R) • z = (e ^ p : R) • z' := by
    rw [hp']
    exact hc
  -- push to the tilde sections over the small basic open
  refine ⟨PrimeSpectrum.basicOpen e, homOfLE heU, ?_, hxe⟩
  show (Scheme.Modules.presheaf (ModuleCat.tilde (ModuleCat.of R
      (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))).map (homOfLE heU).op t =
    (Scheme.Modules.presheaf (ModuleCat.tilde (ModuleCat.of R
      (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))).map (homOfLE heU).op t'
  refine pow_smul_left_cancel (M := ModuleCat.tilde (ModuleCat.of R
    (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))) heg (k + l) ?_
  refine pow_smul_left_cancel (M := ModuleCat.tilde (ModuleCat.of R
    (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))) (le_refl _) p ?_
  have hchain : ∀ (a : ToType (((_root_.PresheafOfModules.toPresheaf _).obj
      ((SheafOfModules.forget _).obj (ModuleCat.tilde (ModuleCat.of R
        (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))))).obj U))
      (ag : Γ(ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))),
        (PrimeSpectrum.basicOpen g : (Spec R).Opens)))
      (w : (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))),
      ag = (Scheme.Modules.presheaf (ModuleCat.tilde (ModuleCat.of R
        (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))).map (homOfLE hgU').op a →
      (g ^ (k + l) : R) • ag =
        (tilde.toOpen (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
          (PrimeSpectrum.basicOpen g)).hom w →
      (e ^ p : R) • ((g ^ (k + l) : R) •
        (show Γ(ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))), (PrimeSpectrum.basicOpen e : (Spec R).Opens)) from
          (Scheme.Modules.presheaf (ModuleCat.tilde (ModuleCat.of R
            (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))).map (homOfLE heU).op a)) =
      (tilde.toOpen (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
        (PrimeSpectrum.basicOpen e)).hom ((e ^ p : R) • w) := by
    intro a ag w hag hgw
    have c1 : (show Γ(ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))), (PrimeSpectrum.basicOpen e : (Spec R).Opens)) from
        (Scheme.Modules.presheaf (ModuleCat.tilde (ModuleCat.of R
          (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))).map (homOfLE heU).op a) =
        (show Γ(ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))), (PrimeSpectrum.basicOpen e : (Spec R).Opens)) from
          (Scheme.Modules.presheaf (ModuleCat.tilde (ModuleCat.of R
            (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))).map (homOfLE heg).op ag) := by
      refine Eq.trans ?_ (congrArg (ConcreteCategory.hom
        ((Scheme.Modules.presheaf (ModuleCat.tilde (ModuleCat.of R
          (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))).map (homOfLE heg).op)) hag.symm)
      exact CategoryTheory.congr_fun ((Scheme.Modules.presheaf
        (ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))).map_comp
          (homOfLE hgU').op (homOfLE heg).op) a
    have c2 : (g ^ (k + l) : R) • (show Γ(ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))), (PrimeSpectrum.basicOpen e : (Spec R).Opens)) from
        (Scheme.Modules.presheaf
        (ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))).map
          (homOfLE heg).op ag) =
        (show Γ(ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))), (PrimeSpectrum.basicOpen e : (Spec R).Opens)) from
          (Scheme.Modules.presheaf (ModuleCat.tilde (ModuleCat.of R
            (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))).map (homOfLE heg).op
              ((g ^ (k + l) : R) • ag)) :=
      (Scheme.Modules.map_smul_Spec (homOfLE heg).op (g ^ (k + l)) ag).symm
    have c3 : (show Γ(ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))), (PrimeSpectrum.basicOpen e : (Spec R).Opens)) from
        (Scheme.Modules.presheaf (ModuleCat.tilde (ModuleCat.of R
          (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))).map (homOfLE heg).op
            ((g ^ (k + l) : R) • ag)) =
        (tilde.toOpen (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
          (PrimeSpectrum.basicOpen e)).hom w := by
      refine Eq.trans (congrArg (ConcreteCategory.hom
        ((Scheme.Modules.presheaf (ModuleCat.tilde (ModuleCat.of R
          (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))))).map (homOfLE heg).op)) hgw) ?_
      rfl
    refine Eq.trans (congrArg (fun v : Γ(ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))), (PrimeSpectrum.basicOpen e : (Spec R).Opens)) ↦ (e ^ p : R) • v)
      ((congrArg (fun v : Γ(ModuleCat.tilde (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))), (PrimeSpectrum.basicOpen e : (Spec R).Opens)) ↦ (g ^ (k + l) : R) • v) c1).trans (c2.trans c3))) ?_
    exact ((tilde.toOpen (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
      (PrimeSpectrum.basicOpen e)).hom.map_smul (e ^ p) w).symm
  have hL := hchain t tg z htg hmz
  have hL' := hchain t' tg' z' htg' hmz'
  exact hL.trans ((congrArg _ hc').trans hL'.symm)

/-- **The tilde comparison is an isomorphism**: on an affine scheme, the exterior power
of the tilde of a module is the tilde of the exterior power. -/
theorem isIso_exteriorPowerTildeComparison :
    IsIso (exteriorPowerTildeComparison M₀ n) :=
  SheafOfModules.isIso_of_isLocallyBijective (exteriorPowerTildeComparison M₀ n)
    (isLocallyInjective_exteriorPowerTildeComparison M₀ n)
    (isLocallySurjective_exteriorPowerTildeComparison M₀ n)

/-- The exterior power of a tilde is the tilde of the exterior power. -/
noncomputable def exteriorPowerTildeIso :
    ModuleCat.tilde
        (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))) ≅
      Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n :=
  letI := isIso_exteriorPowerTildeComparison M₀ n
  asIso (exteriorPowerTildeComparison M₀ n)

/-- The exterior power of a tilde is quasi-coherent. -/
instance : (Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (exteriorPowerTildeIso M₀ n)
    (inferInstance : ((tilde.functor R).obj (ModuleCat.of R
      (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))).IsQuasicoherent)

/-- The global sections of the exterior power of a tilde are the exterior power of the
module: the `R`-linear section isomorphism. -/
noncomputable def exteriorPowerTildeΓEquiv :
    (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)) ≃ₗ[R]
      Γ(Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n, (⊤ : (Spec R).Opens)) := by
  letI := isIso_exteriorPowerTildeComparison M₀ n
  haveI : IsIso ((modulesSpecToSheaf.map (exteriorPowerTildeComparison M₀ n)).1.app
      (.op (⊤ : (Spec R).Opens))) := by
    haveI : IsIso (modulesSpecToSheaf.map (exteriorPowerTildeComparison M₀ n)) :=
      inferInstance
    haveI : IsIso (modulesSpecToSheaf.map (exteriorPowerTildeComparison M₀ n)).1 :=
      inferInstance
    infer_instance
  exact (asIso ((tilde.toOpen
      (ModuleCat.of R (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀)))
      (⊤ : (Spec R).Opens)) ≫
    (modulesSpecToSheaf.map (exteriorPowerTildeComparison M₀ n)).1.app
      (.op (⊤ : (Spec R).Opens)))).toLinearEquiv

/-- The global-sections comparison of the exterior power sends a wedge of elements to the
unit of the wedge of their images in the sections of the tilde. -/
lemma exteriorPowerTildeΓEquiv_ιMulti (v : Fin n → M₀) :
    exteriorPowerTildeΓEquiv M₀ n (_root_.exteriorPower.ιMulti R n v) =
      ((Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n).app
          (.op (⊤ : (Spec R).Opens))).hom
        (_root_.exteriorPower.ιMulti Γ(Spec R, (⊤ : (Spec R).Opens)) n
          (fun i ↦ show Γ(ModuleCat.tilde M₀, (⊤ : (Spec R).Opens)) from
            tilde.toOpen M₀ ⊤ (v i))) := by
  refine Eq.trans (exteriorPowerTildeComparison_toOpen M₀ n ⊤
    (_root_.exteriorPower.ιMulti R n v)) ?_
  exact congrArg (ConcreteCategory.hom
    ((Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n).app
      (.op (⊤ : (Spec R).Opens)))) (wedgeToOpen_ιMulti M₀ n ⊤ v)

/-- **Naturality of the global-sections exterior-power comparison**: on tildes, the
exterior power of a map of modules induces the map of exterior-power sheaves. -/
lemma exteriorPowerTildeΓEquiv_naturality {N₀ : ModuleCat.{u} R} (φ : M₀ ⟶ N₀)
    (w : (⋀[R]^n M₀ : Submodule R (ExteriorAlgebra R M₀))) :
    ((Scheme.Modules.exteriorPowerMap (tilde.map φ) n).app (⊤ : (Spec R).Opens))
        (exteriorPowerTildeΓEquiv M₀ n w) =
      exteriorPowerTildeΓEquiv N₀ n (_root_.exteriorPower.map n φ.hom w) := by
  have hspan : w ∈ Submodule.span R
      (Set.range (_root_.exteriorPower.ιMulti R n (M := M₀))) := by
    rw [_root_.exteriorPower.ιMulti_span]
    trivial
  induction hspan using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨v, rfl⟩ := hw
      have htoOpen : ∀ i, (Scheme.Modules.Hom.app (tilde.map φ) (⊤ : (Spec R).Opens))
            (show Γ(ModuleCat.tilde M₀, (⊤ : (Spec R).Opens)) from
              tilde.toOpen M₀ ⊤ (v i)) =
          (show Γ(ModuleCat.tilde N₀, (⊤ : (Spec R).Opens)) from
            tilde.toOpen N₀ ⊤ (φ (v i))) := fun i ↦
        DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp (tilde.toOpen_map_app φ ⊤)) (v i)
      calc ((Scheme.Modules.exteriorPowerMap (tilde.map φ) n).app
              (⊤ : (Spec R).Opens))
            (exteriorPowerTildeΓEquiv M₀ n (_root_.exteriorPower.ιMulti R n v))
          = ((Scheme.Modules.exteriorPowerMap (tilde.map φ) n).app
              (⊤ : (Spec R).Opens))
            (((Scheme.Modules.toExteriorPower (ModuleCat.tilde M₀) n).app
                (.op (⊤ : (Spec R).Opens))).hom
              (_root_.exteriorPower.ιMulti Γ(Spec R, (⊤ : (Spec R).Opens)) n
                (fun i ↦ show Γ(ModuleCat.tilde M₀, (⊤ : (Spec R).Opens)) from
                  tilde.toOpen M₀ ⊤ (v i)))) :=
            congrArg _ (exteriorPowerTildeΓEquiv_ιMulti M₀ n v)
        _ = ((Scheme.Modules.toExteriorPower (ModuleCat.tilde N₀) n).app
                (.op (⊤ : (Spec R).Opens))).hom
              (_root_.exteriorPower.ιMulti Γ(Spec R, (⊤ : (Spec R).Opens)) n
                (fun i ↦ show Γ(ModuleCat.tilde N₀, (⊤ : (Spec R).Opens)) from
                  (Scheme.Modules.Hom.app (tilde.map φ) (⊤ : (Spec R).Opens))
                    (show Γ(ModuleCat.tilde M₀, (⊤ : (Spec R).Opens)) from
                      tilde.toOpen M₀ ⊤ (v i)))) :=
            Scheme.Modules.exteriorPowerMap_app_unit_ιMulti (tilde.map φ) n ⊤ _
        _ = ((Scheme.Modules.toExteriorPower (ModuleCat.tilde N₀) n).app
                (.op (⊤ : (Spec R).Opens))).hom
              (_root_.exteriorPower.ιMulti Γ(Spec R, (⊤ : (Spec R).Opens)) n
                (fun i ↦ show Γ(ModuleCat.tilde N₀, (⊤ : (Spec R).Opens)) from
                  tilde.toOpen N₀ ⊤ (φ (v i)))) :=
            congrArg _ (congrArg _ (funext htoOpen))
        _ = exteriorPowerTildeΓEquiv N₀ n
              (_root_.exteriorPower.ιMulti R n (fun i ↦ φ (v i))) :=
            (exteriorPowerTildeΓEquiv_ιMulti N₀ n (fun i ↦ φ (v i))).symm
        _ = exteriorPowerTildeΓEquiv N₀ n
              (_root_.exteriorPower.map n φ.hom (_root_.exteriorPower.ιMulti R n v)) :=
            congrArg _ (_root_.exteriorPower.map_apply_ιMulti φ.hom v).symm
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add u v hu hv h1 h2 => rw [map_add, map_add, map_add, map_add, h1, h2]
  | smul r w hw h =>
      have hsmul : ∀ (y : Γ(Scheme.Modules.exteriorPower (ModuleCat.tilde M₀) n,
            (⊤ : (Spec R).Opens))),
          ((Scheme.Modules.exteriorPowerMap (tilde.map φ) n).app
                (⊤ : (Spec R).Opens)) (r • y) =
            r • (show Γ(Scheme.Modules.exteriorPower (ModuleCat.tilde N₀) n,
                (⊤ : (Spec R).Opens)) from
              ((Scheme.Modules.exteriorPowerMap (tilde.map φ) n).app
                (⊤ : (Spec R).Opens)) y) := by
        intro y
        refine Eq.trans (congrArg
          ((Scheme.Modules.exteriorPowerMap (tilde.map φ) n).app
            (⊤ : (Spec R).Opens))
          (algebraMap_smul (R := R) Γ(Spec R, (⊤ : (Spec R).Opens)) r y).symm) ?_
        refine Eq.trans (Scheme.Modules.Hom.app_smul
          (Scheme.Modules.exteriorPowerMap (tilde.map φ) n)
          (algebraMap R Γ(Spec R, (⊤ : (Spec R).Opens)) r) y) ?_
        exact algebraMap_smul (R := R) Γ(Spec R, (⊤ : (Spec R).Opens)) r _
      calc ((Scheme.Modules.exteriorPowerMap (tilde.map φ) n).app
              (⊤ : (Spec R).Opens)) (exteriorPowerTildeΓEquiv M₀ n (r • w))
          = ((Scheme.Modules.exteriorPowerMap (tilde.map φ) n).app
              (⊤ : (Spec R).Opens))
            (r • (exteriorPowerTildeΓEquiv M₀ n w)) :=
            congrArg _ (LinearEquiv.map_smul (exteriorPowerTildeΓEquiv M₀ n) r w)
        _ = r • (show Γ(Scheme.Modules.exteriorPower (ModuleCat.tilde N₀) n,
              (⊤ : (Spec R).Opens)) from
            ((Scheme.Modules.exteriorPowerMap (tilde.map φ) n).app
              (⊤ : (Spec R).Opens)) (exteriorPowerTildeΓEquiv M₀ n w)) :=
            hsmul _
        _ = r • (exteriorPowerTildeΓEquiv N₀ n
              (_root_.exteriorPower.map n φ.hom w)) := congrArg (fun y ↦ r • y) h
        _ = exteriorPowerTildeΓEquiv N₀ n
              (r • _root_.exteriorPower.map n φ.hom w) :=
            (LinearEquiv.map_smul (exteriorPowerTildeΓEquiv N₀ n) r _).symm
        _ = exteriorPowerTildeΓEquiv N₀ n
              (_root_.exteriorPower.map n φ.hom (r • w)) :=
            congrArg _ (LinearMap.map_smul
              (_root_.exteriorPower.map n φ.hom) r w).symm

section QuasicoherentGammaComparison

variable {R : CommRingCat.{u}}

/-- **The exterior power of the global sections of a sheaf on an affine scheme**: the
canonical map from the exterior power of `Γ(M)` to the global sections of `⋀^n M`.  It is
bijective when `M` is quasi-coherent (`bijective_exteriorPowerΓMap`). -/
noncomputable def exteriorPowerΓMap (M : (Spec R).Modules) (n : ℕ) :
    (⋀[R]^n (moduleSpecΓFunctor.obj M) :
        Submodule R (ExteriorAlgebra R (moduleSpecΓFunctor.obj M))) →
      Γ(Scheme.Modules.exteriorPower M n, (⊤ : (Spec R).Opens)) :=
  fun w ↦ (Scheme.Modules.exteriorPowerMap (Scheme.Modules.fromTildeΓ M) n).app
    (⊤ : (Spec R).Opens)
    (exteriorPowerTildeΓEquiv (moduleSpecΓFunctor.obj M) n w)



/-- The comparison `⋀^n Γ(M) → Γ(⋀^n M)` as an `R`-linear map. -/
noncomputable def exteriorPowerΓMapₗ (M : (Spec R).Modules) (n : ℕ) :
    (⋀[R]^n (moduleSpecΓFunctor.obj M) :
        Submodule R (ExteriorAlgebra R (moduleSpecΓFunctor.obj M))) →ₗ[R]
      moduleSpecΓFunctor.obj (Scheme.Modules.exteriorPower M n) :=
  (moduleSpecΓFunctor.map
      (Scheme.Modules.exteriorPowerMap (Scheme.Modules.fromTildeΓ M) n)).hom ∘ₗ
    (exteriorPowerTildeΓEquiv (moduleSpecΓFunctor.obj M) n).toLinearMap

@[simp]
lemma exteriorPowerΓMapₗ_apply (M : (Spec R).Modules) (n : ℕ)
    (w : (⋀[R]^n (moduleSpecΓFunctor.obj M) :
      Submodule R (ExteriorAlgebra R (moduleSpecΓFunctor.obj M)))) :
    exteriorPowerΓMapₗ M n w = exteriorPowerΓMap M n w := rfl

/-- The comparison sends a wedge of global sections to the sheafification unit of that
wedge. -/
lemma exteriorPowerΓMap_ιMulti (M : (Spec R).Modules) (n : ℕ)
    (v : Fin n → moduleSpecΓFunctor.obj M) :
    exteriorPowerΓMap M n (_root_.exteriorPower.ιMulti R n v) =
      ((Scheme.Modules.toExteriorPower M n).app
        (.op (⊤ : (Spec R).Opens))).hom
        (_root_.exteriorPower.ιMulti Γ(Spec R, (⊤ : (Spec R).Opens)) n
          (fun i ↦ show Γ(M, (⊤ : (Spec R).Opens)) from v i)) := by
  refine Eq.trans (congrArg
    ((Scheme.Modules.exteriorPowerMap (Scheme.Modules.fromTildeΓ M) n).app
      (⊤ : (Spec R).Opens))
    (exteriorPowerTildeΓEquiv_ιMulti (moduleSpecΓFunctor.obj M) n v)) ?_
  refine Eq.trans (Scheme.Modules.exteriorPowerMap_app_unit_ιMulti
    (Scheme.Modules.fromTildeΓ M) n (⊤ : (Spec R).Opens) _) ?_
  refine congrArg _ (congrArg
    (_root_.exteriorPower.ιMulti Γ(Spec R, (⊤ : (Spec R).Opens)) n) (funext fun i ↦ ?_))
  have h := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp
    (Scheme.Modules.toOpen_fromTildeΓ_app M (⊤ : (Spec R).Opens))) (v i)
  refine Eq.trans h ?_
  have hid : (homOfLE (le_top (a := (⊤ : (Spec R).Opens)))) = 𝟙 (⊤ : (Spec R).Opens) :=
    Subsingleton.elim _ _
  rw [hid, op_id, CategoryTheory.Functor.map_id]
  rfl

/-- **Naturality of the global-sections comparison for exterior powers** on an affine
scheme: for any morphism of sheaves of modules, the induced map of exterior powers is on
global sections the exterior power of the induced map of modules. -/
lemma exteriorPowerΓMap_naturality {M N : (Spec R).Modules} (ψ : M ⟶ N) (n : ℕ)
    (w : (⋀[R]^n (moduleSpecΓFunctor.obj M) :
      Submodule R (ExteriorAlgebra R (moduleSpecΓFunctor.obj M)))) :
    ((Scheme.Modules.exteriorPowerMap ψ n).app (⊤ : (Spec R).Opens))
        (exteriorPowerΓMap M n w) =
      exteriorPowerΓMap N n
        (_root_.exteriorPower.map n (moduleSpecΓFunctor.map ψ).hom w) := by
  have hnat : Scheme.Modules.fromTildeΓ M ≫ ψ =
      tilde.map (moduleSpecΓFunctor.map ψ) ≫ Scheme.Modules.fromTildeΓ N :=
    (Scheme.Modules.fromTildeΓNatTrans.naturality ψ).symm
  calc ((Scheme.Modules.exteriorPowerMap ψ n).app (⊤ : (Spec R).Opens))
        (exteriorPowerΓMap M n w)
      = ((Scheme.Modules.exteriorPowerMap
            (Scheme.Modules.fromTildeΓ M ≫ ψ) n).app (⊤ : (Spec R).Opens))
          (exteriorPowerTildeΓEquiv (moduleSpecΓFunctor.obj M) n w) := by
        rw [Scheme.Modules.exteriorPowerMap_comp, Scheme.Modules.Hom.comp_app]
        rfl
    _ = ((Scheme.Modules.exteriorPowerMap
          (tilde.map (moduleSpecΓFunctor.map ψ) ≫
            Scheme.Modules.fromTildeΓ N) n).app (⊤ : (Spec R).Opens))
          (exteriorPowerTildeΓEquiv (moduleSpecΓFunctor.obj M) n w) := by
        rw [hnat]
        rfl
    _ = ((Scheme.Modules.exteriorPowerMap
            (Scheme.Modules.fromTildeΓ N) n).app (⊤ : (Spec R).Opens))
          (((Scheme.Modules.exteriorPowerMap
              (tilde.map (moduleSpecΓFunctor.map ψ)) n).app (⊤ : (Spec R).Opens))
            (exteriorPowerTildeΓEquiv (moduleSpecΓFunctor.obj M) n w)) := by
        rw [Scheme.Modules.exteriorPowerMap_comp, Scheme.Modules.Hom.comp_app]
        rfl
    _ = exteriorPowerΓMap N n
          (_root_.exteriorPower.map n (moduleSpecΓFunctor.map ψ).hom w) :=
        congrArg _ (exteriorPowerTildeΓEquiv_naturality
          (moduleSpecΓFunctor.obj M) n (moduleSpecΓFunctor.map ψ) w)

/-- For a quasi-coherent sheaf on an affine scheme the comparison is bijective. -/
lemma bijective_exteriorPowerΓMap (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    Function.Bijective (exteriorPowerΓMap M n) := by
  haveI : IsIso (Scheme.Modules.fromTildeΓ M) :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  haveI : IsIso (Scheme.Modules.exteriorPowerMap (Scheme.Modules.fromTildeΓ M) n) :=
    (Scheme.Modules.exteriorPowerIso (asIso (Scheme.Modules.fromTildeΓ M)) n).isIso_hom
  have hbij : Function.Bijective
      ((Scheme.Modules.exteriorPowerMap (Scheme.Modules.fromTildeΓ M) n).app
        (⊤ : (Spec R).Opens)) := by
    refine (ConcreteCategory.bijective_of_isIso
      ((Scheme.Modules.exteriorPowerMap (Scheme.Modules.fromTildeΓ M) n).app
        (⊤ : (Spec R).Opens)))
  exact hbij.comp (exteriorPowerTildeΓEquiv (moduleSpecΓFunctor.obj M) n).bijective

end QuasicoherentGammaComparison

end AlgebraicGeometry

end
