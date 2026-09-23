module

public import StacksAndModuli.API.LinearMapFiniteFreeZeroLocus
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Affine zero loci for morphisms of sheaves

This file is the affine-scheme bridge between a vanishing condition on a pulled-back
sheaf morphism and the coefficient-ideal construction in
`LinearMapFiniteFreeZeroLocus`.

There are two layers.

* `Scheme.Modules.TildePullbackComparison` records the standard naturality square
  identifying pullback of a morphism between tilde sheaves with a specified
  base-changed module map.  From this square, vanishing of the pulled-back sheaf map
  is equivalent to vanishing of the module map.
* `Scheme.Modules.pullback_tildeMap_eq_zero_iff_unique_zeroLocusLift_canonical`
  constructs the comparison automatically for a map into a finite free module and
  gives the affine closed-zero-locus universal property.
* `Scheme.Modules.HasFiniteFreeVanishingModel` packages the precise finite-coordinate
  output needed from relative Serre vanishing and Cohomology and Base Change for a
  general proper family.  It constructs a closed subscheme of an affine base and proves
  its universal property on affine test schemes.

For a morphism on relative projective space, the remaining geometric task is to
construct `HasFiniteFreeVanishingModel`: choose a sufficiently positive finite
twisted-free presentation of the source and identify the resulting finite module of
maps into the flat target compatibly with arbitrary base change.  No such assertion is
assumed implicitly here.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open TensorProduct
open scoped ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Modules

section TildeComparison

variable {R A : CommRingCat.{u}}
variable {M N : Type u} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
variable {M' N' : Type u} [AddCommGroup M'] [Module A M']
  [AddCommGroup N'] [Module A N']

/-- Global sections of pushforward along an affine-spectrum morphism are restriction
of scalars.  This is the right-adjoint comparison used to construct affine tilde base
change. -/
noncomputable def affinePushforwardGlobalSectionsIso (f : R ⟶ A) :
    pushforward (Spec.map f) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars f.hom :=
  Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso f)
    (TopCat.Sheaf.forget _ _ ⋙ (CategoryTheory.evaluation _ _).obj (.op ⊤))

/-- Pullback of a tilde sheaf along a morphism of affine spectra is extension of
scalars.  It is constructed by uniqueness of left adjoints from the corresponding
global-sections comparison. -/
noncomputable def affineTildePullbackIso (f : R ⟶ A) :
    AlgebraicGeometry.tilde.functor R ⋙ pullback (Spec.map f) ≅
      ModuleCat.extendScalars f.hom ⋙ AlgebraicGeometry.tilde.functor A :=
  Adjunction.leftAdjointCompIso AlgebraicGeometry.tilde.adjunction
    (pullbackPushforwardAdjunction (Spec.map f))
    ((ModuleCat.extendRestrictScalarsAdj f.hom).comp
      AlgebraicGeometry.tilde.adjunction)
    (affinePushforwardGlobalSectionsIso f)

/-- A naturality square identifying pullback of a morphism of affine tilde sheaves
with a specified module map over the target affine ring.

This is deliberately stronger than merely assuming an equivalence of zero conditions:
the two vertical maps are actual sheaf isomorphisms and `naturality` is the comparison
square one obtains from functorial affine base change. -/
structure TildePullbackComparison
    (g : Spec A ⟶ Spec R) (l : M →ₗ[R] N) (l' : M' →ₗ[A] N') where
  /-- Comparison for the source module. -/
  sourceIso :
    (pullback g).obj (AlgebraicGeometry.tilde (ModuleCat.of R M)) ≅
      AlgebraicGeometry.tilde (ModuleCat.of A M')
  /-- Comparison for the target module. -/
  targetIso :
    (pullback g).obj (AlgebraicGeometry.tilde (ModuleCat.of R N)) ≅
      AlgebraicGeometry.tilde (ModuleCat.of A N')
  /-- Naturality of the comparisons with respect to the module map. -/
  naturality :
    (pullback g).map
          ((AlgebraicGeometry.tilde.functor R).map (ModuleCat.ofHom l)) ≫
        targetIso.hom =
      sourceIso.hom ≫
        (AlgebraicGeometry.tilde.functor A).map (ModuleCat.ofHom l')

namespace TildePullbackComparison

/-- The canonical tilde pullback comparison for extension of scalars. -/
noncomputable def ofExtendScalars
    (f : R ⟶ A) (l : M →ₗ[R] N) :
    TildePullbackComparison (Spec.map f) l
      (((ModuleCat.extendScalars f.hom).map (ModuleCat.ofHom l)).hom) where
  sourceIso := (affineTildePullbackIso f).app (ModuleCat.of R M)
  targetIso := (affineTildePullbackIso f).app (ModuleCat.of R N)
  naturality := (affineTildePullbackIso f).hom.naturality (ModuleCat.ofHom l)

/-- Under a tilde pullback comparison, the pulled-back sheaf morphism vanishes exactly
when the specified base-changed module map vanishes. -/
lemma pullback_map_eq_zero_iff
    {g : Spec A ⟶ Spec R} {l : M →ₗ[R] N} {l' : M' →ₗ[A] N'}
    (C : TildePullbackComparison g l l') :
    (pullback g).map
        ((AlgebraicGeometry.tilde.functor R).map (ModuleCat.ofHom l)) = 0 ↔
      l' = 0 := by
  constructor
  · intro h
    have htilde :
        (AlgebraicGeometry.tilde.functor A).map (ModuleCat.ofHom l') = 0 := by
      apply (cancel_epi C.sourceIso.hom).mp
      rw [← C.naturality, h]
      simp
    have hmodule : ModuleCat.ofHom l' = 0 := by
      apply (AlgebraicGeometry.tilde.functor A).map_injective
      simpa using htilde
    exact congrArg ModuleCat.Hom.hom hmodule
  · intro h
    have hmodule : ModuleCat.ofHom l' = 0 := by
      apply ModuleCat.hom_ext
      exact h
    have htilde :
        (AlgebraicGeometry.tilde.functor A).map (ModuleCat.ofHom l') = 0 := by
      rw [hmodule]
      exact AlgebraicGeometry.tilde.map_zero
    apply (cancel_mono C.targetIso.hom).mp
    rw [C.naturality, htilde]
    simp

end TildePullbackComparison

variable {r : ℕ}

/-- The tilde sheaf morphism associated to the scalar extension of a map into a finite
free module. -/
noncomputable def finiteFreeBaseChangeTildeMap
    (φ : M →ₗ[R] (Fin r → R)) (f : R ⟶ A) :
    letI : Algebra R A := f.hom.toAlgebra
    AlgebraicGeometry.tilde (ModuleCat.of A (A ⊗[R] M)) ⟶
      AlgebraicGeometry.tilde (ModuleCat.of A (Fin r → A)) := by
  letI : Algebra R A := f.hom.toAlgebra
  exact (AlgebraicGeometry.tilde.functor A).map
    (ModuleCat.ofHom (φ.baseChangeToPi f.hom))

/-- The standard affine base-change square needed to compare pullback of `φ̃` with
the tilde of `A ⊗_R φ`, after identifying `A ⊗_R R^r` with `A^r`. -/
abbrev FiniteFreeTildePullbackComparison
    (φ : M →ₗ[R] (Fin r → R)) (f : R ⟶ A) :=
  letI : Algebra R A := f.hom.toAlgebra
  TildePullbackComparison
    (Spec.map f) φ (φ.baseChangeToPi f.hom)

/-- Extension of scalars of the finite free module `R^r` is canonically `A^r`.

The algebra instance here is the one used internally by
`ModuleCat.extendScalars`; keeping it explicit makes the source of the isomorphism
definitionally equal to the functor value. -/
noncomputable def finiteFreeExtendScalarsIso (f : R ⟶ A) :
    (ModuleCat.extendScalars f.hom).obj (ModuleCat.of R (Fin r → R)) ≅
      ModuleCat.of A (Fin r → A) := by
  letI : Algebra R A := ((algebraMap A A).comp f.hom).toAlgebra
  exact (TensorProduct.piScalarRight R A A (Fin r)).toModuleIso

/-- Formula for the finite-free extension-of-scalars isomorphism on pure tensors. -/
@[simp]
lemma finiteFreeExtendScalarsIso_hom_tmul_apply
    (f : R ⟶ A) (a : A) (v : Fin r → R) (i : Fin r) :
    (finiteFreeExtendScalarsIso f).hom.hom (a ⊗ₜ[R, f.hom] v) i =
      a * f.hom (v i) := by
  letI : Algebra R A := ((algebraMap A A).comp f.hom).toAlgebra
  change (TensorProduct.piScalarRight R A A (Fin r) (a ⊗ₜ[R] v)) i = _
  rw [TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]
  simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra, mul_comm]

/-- Categorical extension of scalars of a map `M → R^r`, followed by the standard
identification `A ⊗_R R^r ≃ A^r`. -/
noncomputable def finiteFreeExtendScalarsMap
    (φ : M →ₗ[R] (Fin r → R)) (f : R ⟶ A) :
    (ModuleCat.extendScalars f.hom).obj (ModuleCat.of R M) ⟶
      ModuleCat.of A (Fin r → A) :=
  (ModuleCat.extendScalars f.hom).map (ModuleCat.ofHom φ) ≫
    (finiteFreeExtendScalarsIso f).hom

/-- The categorical finite-free scalar extension vanishes exactly when the ring map
kills every coefficient of the original map. -/
lemma finiteFreeExtendScalarsMap_eq_zero_iff_apply
    (φ : M →ₗ[R] (Fin r → R)) (f : R ⟶ A) :
    finiteFreeExtendScalarsMap φ f = 0 ↔
      ∀ (m : M) (i : Fin r), f.hom (φ m i) = 0 := by
  letI : Algebra R A := ((algebraMap A A).comp f.hom).toAlgebra
  constructor
  · intro h m i
    have h' := congrArg ModuleCat.Hom.hom h
    have h'' := LinearMap.congr_fun h' ((1 : A) ⊗ₜ[R] m)
    have h''' := congrFun h'' i
    change
      ((finiteFreeExtendScalarsIso f).hom.hom
        (((ModuleCat.extendScalars f.hom).map (ModuleCat.ofHom φ)).hom
          ((1 : A) ⊗ₜ[R] m))) i = 0 at h'''
    rw [ModuleCat.ExtendScalars.map_tmul] at h'''
    rw [finiteFreeExtendScalarsIso_hom_tmul_apply] at h'''
    simpa using h'''
  · intro h
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    ext i
    change
      ((finiteFreeExtendScalarsIso f).hom.hom
        (((ModuleCat.extendScalars f.hom).map (ModuleCat.ofHom φ)).hom
          ((1 : A) ⊗ₜ[R] m))) i = 0
    rw [ModuleCat.ExtendScalars.map_tmul]
    rw [finiteFreeExtendScalarsIso_hom_tmul_apply]
    simpa using h m i

/-- Vanishing of the raw categorical extension of scalars is unchanged by the
finite-free target identification. -/
lemma extendScalarsMap_hom_eq_zero_iff_finiteFreeExtendScalarsMap_eq_zero
    (φ : M →ₗ[R] (Fin r → R)) (f : R ⟶ A) :
    ((ModuleCat.extendScalars f.hom).map (ModuleCat.ofHom φ)).hom = 0 ↔
      finiteFreeExtendScalarsMap φ f = 0 := by
  constructor
  · intro h
    have hq :
        (ModuleCat.extendScalars f.hom).map (ModuleCat.ofHom φ) = 0 := by
      apply ModuleCat.hom_ext
      exact h
    simp [finiteFreeExtendScalarsMap, hq]
  · intro h
    have hcomp :
        (ModuleCat.extendScalars f.hom).map (ModuleCat.ofHom φ) ≫
            (finiteFreeExtendScalarsIso f).hom = 0 := by
      simpa only [finiteFreeExtendScalarsMap] using h
    have hq :
        (ModuleCat.extendScalars f.hom).map (ModuleCat.ofHom φ) = 0 := by
      apply (cancel_mono (finiteFreeExtendScalarsIso f).hom).mp
      simpa using hcomp
    exact congrArg ModuleCat.Hom.hom hq

/-- The categorical scalar-extension map and the explicit tensor-product map from
`LinearMapFiniteFreeZeroLocus` have the same vanishing condition. -/
lemma finiteFreeExtendScalarsMap_eq_zero_iff_baseChangeToPi
    (φ : M →ₗ[R] (Fin r → R)) (f : R ⟶ A) :
    finiteFreeExtendScalarsMap φ f = 0 ↔
      (letI : Algebra R A := f.hom.toAlgebra;
        φ.baseChangeToPi f.hom = 0) := by
  rw [finiteFreeExtendScalarsMap_eq_zero_iff_apply,
    LinearMap.baseChangeToPi_eq_zero_iff_apply]

/-- A finite-free affine tilde comparison turns pulled-back sheaf vanishing into the
coefficient-linear-map vanishing condition. -/
lemma pullback_tildeMap_eq_zero_iff_baseChangeToPi
    (φ : M →ₗ[R] (Fin r → R)) (f : R ⟶ A)
    (C : FiniteFreeTildePullbackComparison φ f) :
    (pullback (Spec.map f)).map
        ((AlgebraicGeometry.tilde.functor R).map (ModuleCat.ofHom φ)) = 0 ↔
      (letI : Algebra R A := f.hom.toAlgebra; φ.baseChangeToPi f.hom = 0) :=
  C.pullback_map_eq_zero_iff

/-- Pullback of a finite-free-valued affine tilde morphism vanishes exactly when its
canonical scalar extension vanishes; no separately supplied comparison is needed. -/
lemma pullback_tildeMap_eq_zero_iff_baseChangeToPi_canonical
    (φ : M →ₗ[R] (Fin r → R)) (f : R ⟶ A) :
    (pullback (Spec.map f)).map
        ((AlgebraicGeometry.tilde.functor R).map (ModuleCat.ofHom φ)) = 0 ↔
      (letI : Algebra R A := f.hom.toAlgebra; φ.baseChangeToPi f.hom = 0) :=
  (TildePullbackComparison.ofExtendScalars f φ).pullback_map_eq_zero_iff.trans <|
    (extendScalarsMap_hom_eq_zero_iff_finiteFreeExtendScalarsMap_eq_zero φ f).trans
      (finiteFreeExtendScalarsMap_eq_zero_iff_baseChangeToPi φ f)

/-- The affine zero locus of a finite-free-valued tilde morphism has the expected
universal property, provided the standard affine pullback comparison is supplied. -/
lemma pullback_tildeMap_eq_zero_iff_exists_zeroLocusLift
    (φ : M →ₗ[R] (Fin r → R)) (f : R ⟶ A)
    (C : FiniteFreeTildePullbackComparison φ f) :
    (pullback (Spec.map f)).map
        ((AlgebraicGeometry.tilde.functor R).map (ModuleCat.ofHom φ)) = 0 ↔
      ∃ h : Spec A ⟶ φ.zeroLocus,
        h ≫ φ.zeroLocusι = Spec.map f := by
  rw [pullback_tildeMap_eq_zero_iff_baseChangeToPi φ f C]
  exact φ.baseChangeToPi_eq_zero_iff_exists_zeroLocusLift f.hom

/-- Unique form of the affine tilde zero-locus universal property. -/
lemma pullback_tildeMap_eq_zero_iff_unique_zeroLocusLift
    (φ : M →ₗ[R] (Fin r → R)) (f : R ⟶ A)
    (C : FiniteFreeTildePullbackComparison φ f) :
    (pullback (Spec.map f)).map
        ((AlgebraicGeometry.tilde.functor R).map (ModuleCat.ofHom φ)) = 0 ↔
      ∃! h : Spec A ⟶ φ.zeroLocus,
        h ≫ φ.zeroLocusι = Spec.map f := by
  rw [pullback_tildeMap_eq_zero_iff_baseChangeToPi φ f C]
  exact φ.baseChangeToPi_eq_zero_iff_unique_zeroLocusLift f.hom

/-- Canonical affine zero-locus universal property for the tilde of a map into a
finite free module.  The affine tilde base-change comparison is constructed
internally. -/
lemma pullback_tildeMap_eq_zero_iff_exists_zeroLocusLift_canonical
    (φ : M →ₗ[R] (Fin r → R)) (f : R ⟶ A) :
    (pullback (Spec.map f)).map
        ((AlgebraicGeometry.tilde.functor R).map (ModuleCat.ofHom φ)) = 0 ↔
      ∃ h : Spec A ⟶ φ.zeroLocus,
        h ≫ φ.zeroLocusι = Spec.map f := by
  rw [pullback_tildeMap_eq_zero_iff_baseChangeToPi_canonical φ f]
  exact φ.baseChangeToPi_eq_zero_iff_exists_zeroLocusLift f.hom

/-- Unique canonical affine zero-locus factorization for the tilde of a map into a
finite free module. -/
lemma pullback_tildeMap_eq_zero_iff_unique_zeroLocusLift_canonical
    (φ : M →ₗ[R] (Fin r → R)) (f : R ⟶ A) :
    (pullback (Spec.map f)).map
        ((AlgebraicGeometry.tilde.functor R).map (ModuleCat.ofHom φ)) = 0 ↔
      ∃! h : Spec A ⟶ φ.zeroLocus,
        h ≫ φ.zeroLocusι = Spec.map f := by
  rw [pullback_tildeMap_eq_zero_iff_baseChangeToPi_canonical φ f]
  exact φ.baseChangeToPi_eq_zero_iff_unique_zeroLocusLift f.hom

end TildeComparison

section FiniteVanishingModel

variable {R : Type u} [CommRing R]
variable {X : Scheme.{u}} (pX : X ⟶ Spec (.of R))
variable {E F : X.Modules} (p : E ⟶ F)

/-- A finite base-ring coordinate model for universal vanishing of a sheaf morphism.

For every affine base change `Spec A → Spec R`, the pullback of `p` to the cartesian
base change of `X` is zero exactly when the scalar extension of `coordinates` is zero.
The source module of `coordinates` is required to be finite, matching the output of a
finite twisted-free presentation in the projective application.

For coherent sheaves `E → F` on projective space with `F` flat over the base, relative
Serre vanishing and Cohomology and Base Change are expected to construct this structure.
-/
structure HasFiniteFreeVanishingModel where
  /-- The finite module of equations before choosing finite-free coordinates. -/
  M : Type u
  [addCommGroup : AddCommGroup M]
  [module : Module R M]
  [finite : Module.Finite R M]
  /-- Rank of the finite free module in which the equations are recorded. -/
  r : ℕ
  /-- The base-ring linear map whose coordinates are the defining equations. -/
  coordinates : M →ₗ[R] (Fin r → R)
  /-- Pullback vanishing is detected by those coordinates after every affine base
  change. -/
  pullback_zero_iff : ∀ (A : Type u) [CommRing A] (f : R →+* A),
    (pullback
        (Limits.pullback.snd (Spec.map (CommRingCat.ofHom f)) pX)).map p = 0 ↔
      (letI : Algebra R A := f.toAlgebra;
        coordinates.baseChangeToPi f = 0)

namespace HasFiniteFreeVanishingModel

attribute [instance] addCommGroup module finite

/-- The coefficient ideal defining the vanishing locus. -/
def ideal (H : HasFiniteFreeVanishingModel pX p) : Ideal R :=
  H.coordinates.coefficientIdeal

/-- The defining ideal is finitely generated. -/
lemma ideal_fg (H : HasFiniteFreeVanishingModel pX p) : H.ideal.FG :=
  H.coordinates.coefficientIdeal_fg

/-- The universal closed affine zero locus. -/
noncomputable abbrev zeroLocus (H : HasFiniteFreeVanishingModel pX p) : Scheme :=
  H.coordinates.zeroLocus

/-- Inclusion of the universal zero locus into the affine base. -/
noncomputable abbrev zeroLocusι (H : HasFiniteFreeVanishingModel pX p) :
    H.zeroLocus ⟶ Spec (.of R) :=
  H.coordinates.zeroLocusι

instance (H : HasFiniteFreeVanishingModel pX p) : IsClosedImmersion H.zeroLocusι :=
  LinearMap.instIsClosedImmersionZeroLocusι H.coordinates

/-- The zero locus as an object over the affine base. -/
noncomputable def zeroLocusOver (H : HasFiniteFreeVanishingModel pX p) :
    Over (Spec (.of R)) :=
  Over.mk H.zeroLocusι

/-- Universal property on affine test schemes: the pulled-back sheaf morphism vanishes
exactly when the affine test morphism factors through the closed zero locus. -/
lemma pullback_eq_zero_iff_exists_zeroLocusLift
    (H : HasFiniteFreeVanishingModel pX p)
    (A : Type u) [CommRing A] (f : R →+* A) :
    (pullback
        (Limits.pullback.snd (Spec.map (CommRingCat.ofHom f)) pX)).map p = 0 ↔
      ∃ h : Spec (.of A) ⟶ H.zeroLocus,
        h ≫ H.zeroLocusι = Spec.map (CommRingCat.ofHom f) := by
  rw [H.pullback_zero_iff A f]
  exact H.coordinates.baseChangeToPi_eq_zero_iff_exists_zeroLocusLift f

/-- Unique form of the affine universal property. -/
lemma pullback_eq_zero_iff_unique_zeroLocusLift
    (H : HasFiniteFreeVanishingModel pX p)
    (A : Type u) [CommRing A] (f : R →+* A) :
    (pullback
        (Limits.pullback.snd (Spec.map (CommRingCat.ofHom f)) pX)).map p = 0 ↔
      ∃! h : Spec (.of A) ⟶ H.zeroLocus,
        h ≫ H.zeroLocusι = Spec.map (CommRingCat.ofHom f) := by
  rw [H.pullback_zero_iff A f]
  exact H.coordinates.baseChangeToPi_eq_zero_iff_unique_zeroLocusLift f

/-- Over-category form of the affine universal property, matching the factorization
shape used by relative representability arguments. -/
lemma pullback_eq_zero_iff_nonempty_overHom
    (H : HasFiniteFreeVanishingModel pX p)
    (A : Type u) [CommRing A] (f : R →+* A) :
    (pullback
        (Limits.pullback.snd (Spec.map (CommRingCat.ofHom f)) pX)).map p = 0 ↔
      Nonempty (Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ H.zeroLocusOver) := by
  rw [pullback_eq_zero_iff_exists_zeroLocusLift (pX := pX) (p := p) H A f]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨Over.homMk h hh⟩
  · rintro ⟨h⟩
    exact ⟨h.left, h.w⟩

end HasFiniteFreeVanishingModel

end FiniteVanishingModel

end AlgebraicGeometry.Scheme.Modules
