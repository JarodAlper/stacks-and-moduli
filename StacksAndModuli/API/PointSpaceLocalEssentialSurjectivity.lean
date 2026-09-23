module

public import StacksAndModuli.API.BasedFunctorLocalEssentialSurjectivity
public import StacksAndModuli.«Section4.3-Properties».«part4.3.4-topological-space»

/-!
# Locally essentially surjective morphisms and point spaces

A morphism of prestacks which is locally essentially surjective for the big étale
topology is surjective on field-valued point classes. Given a point over a field, an
étale covering sieve supplies a covering scheme and a point above the unique point of
the field spectrum. Passing to the residue field of that point produces the required
field extension and a local lift. The two-Yoneda lemma turns the lifted object into a
field-valued point of the source.

## Main result

* `AlgebraicGeometry.BasedFunctor.surjective_mapPoints_of_locallyEssentiallySurjective`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Opposite AlgebraicGeometry
  CategoryTheory.BasedCategory AlgebraicGeometry.BasedCategory

universe v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry.BasedFunctor

variable {𝒜 : BasedCategory.{v₂, u₂} Scheme.{u}}
  {ℬ : BasedCategory.{v₃, u₃} Scheme.{u}}

/-- A morphism which is locally essentially surjective for the big étale topology is
surjective on field-valued point classes. -/
theorem surjective_mapPoints_of_locallyEssentiallySurjective
    [𝒜.p.IsFiberedInGroupoids] [ℬ.p.IsFiberedInGroupoids]
    (F : BasedFunctor 𝒜 ℬ)
    (hF : F.IsLocallyEssentiallySurjective (J := Scheme.etaleTopology)) :
    Function.Surjective (mapPoints F) := by
  intro v
  induction v using pointSpace.ind with
  | _ y =>
  let S₀ : Scheme.{u} := Spec (CommRingCat.of y.carrier)
  let ZS : Over S₀ := Over.mk (𝟙 S₀)
  let d : ℬ.obj := y.hom.obj ZS
  let S : Scheme.{u} := ℬ.p.obj d
  have hd : S = S₀ := y.hom.w_obj ZS
  obtain ⟨R, hR, hlift⟩ := hF d
  obtain ⟨R₀, hR₀, hR₀R⟩ :=
    Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition.mp hR
  obtain ⟨𝒰, h𝒰eq⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hR₀
  have hSnonempty : Nonempty S := hd.symm ▸ (inferInstance : Nonempty S₀)
  obtain ⟨pt⟩ := hSnonempty
  obtain ⟨k, x, -⟩ := Scheme.Cover.exists_eq 𝒰 pt
  let T : Scheme.{u} := 𝒰.X k
  let f : T ⟶ S := 𝒰.f k
  have hfR : R f := by
    apply hR₀R
    rw [h𝒰eq]
    exact ⟨k⟩
  let L : Type u := T.residueField x
  let ρ : Spec (CommRingCat.of L) ⟶ T := T.fromSpecResidueField x
  let φ₀ : Spec (CommRingCat.of L) ⟶ S := ρ ≫ f
  have hφ₀R : R φ₀ := R.downward_closed hfR ρ
  obtain ⟨a, q, hq⟩ := hlift φ₀ hφ₀R
  let _ : IsHomLift ℬ.p φ₀ q := hq
  have ha : 𝒜.p.obj a = Spec (CommRingCat.of L) :=
    (F.w_obj a).symm.trans (IsHomLift.domain_eq ℬ.p φ₀ q)
  let E := twoYonedaEval (𝒳 := 𝒜) (Spec (CommRingCat.of L))
  let _ : E.IsEquivalence := isEquivalence_twoYonedaEval
    (𝒳 := 𝒜) (Spec (CommRingCat.of L))
  let z : BasedFunctor (overBased (Spec (CommRingCat.of L))) 𝒜 :=
    E.objPreimage (Functor.Fiber.mk ha)
  let ez : E.obj z ≅ Functor.Fiber.mk ha :=
    E.objObjPreimageIso (Functor.Fiber.mk ha)
  let φ : Spec (CommRingCat.of L) ⟶ S₀ := φ₀ ≫ eqToHom hd
  have hq' : IsHomLift ℬ.p φ q := by
    apply IsHomLift.of_fac ℬ.p φ q
      (IsHomLift.domain_eq ℬ.p φ₀ q) hd
    have hfac := IsHomLift.fac ℬ.p φ₀ q
    dsimp [φ]
    calc
      φ₀ ≫ eqToHom hd =
          (eqToHom (IsHomLift.domain_eq ℬ.p φ₀ q).symm ≫
            ℬ.p.map q ≫ eqToHom (IsHomLift.codomain_eq ℬ.p φ₀ q)) ≫
              eqToHom hd := congrArg (fun κ => κ ≫ eqToHom hd) hfac
      _ = eqToHom (IsHomLift.domain_eq ℬ.p φ₀ q).symm ≫
          ℬ.p.map q ≫ eqToHom hd := by simp
  let _ : IsHomLift ℬ.p φ q := hq'
  let t : (Over.mk φ : Over S₀) ⟶ ZS := Over.homMk φ
  have hyt : IsHomLift ℬ.p φ (y.hom.map t) := by
    have := basedMap_isHomLift_left S₀ (F := y.hom) t
    simpa [t, ZS] using this
  let _ : IsHomLift ℬ.p φ (y.hom.map t) := hyt
  let e₀ : F.obj a ≅ y.hom.obj (Over.mk φ) :=
    IsCartesian.domainUniqueUpToIso ℬ.p φ (y.hom.map t) q
  have he₀ : IsHomLift ℬ.p (𝟙 (Spec (CommRingCat.of L))) e₀.hom := by
    exact IsCartesian.domainUniqueUpToIso_inv_isHomLift
      ℬ.p φ (y.hom.map t) q
  let e₁ : F.obj (z.obj (Over.mk (𝟙 (Spec (CommRingCat.of L))))) ≅
      y.hom.obj (Over.mk φ) :=
    (F.toFunctor.mapIso (Fiber.fiberInclusion.mapIso ez)).trans e₀
  have he₁ : IsHomLift ℬ.p (𝟙 (Spec (CommRingCat.of L))) e₁.hom := by
    dsimp [e₁]
    infer_instance
  let ψ : y.carrier →+* L := (Spec.preimage φ).hom
  have hspec : Spec.map (CommRingCat.ofHom ψ) = φ := by
    change Spec.map (CommRingCat.ofHom (Spec.preimage φ).hom) = φ
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hyobj : (y.restrict ψ).obj (Over.mk (𝟙 (Spec (CommRingCat.of L)))) =
      y.hom.obj (Over.mk φ) := by
    change y.hom.obj ((overBased.map (Spec.map (CommRingCat.ofHom ψ))).obj
      (Over.mk (𝟙 (Spec (CommRingCat.of L))))) = _
    rw [hspec]
    rfl
  let e₂ : (z.comp F).obj (Over.mk (𝟙 (Spec (CommRingCat.of L)))) ≅
      (y.restrict ψ).obj (Over.mk (𝟙 (Spec (CommRingCat.of L)))) :=
    e₁.trans (eqToIso hyobj.symm)
  have he₂ : IsHomLift ℬ.p (𝟙 (Spec (CommRingCat.of L))) e₂.hom := by
    dsimp [e₂]
    infer_instance
  obtain ⟨e⟩ :=
    AlgebraicGeometry.BasedCategory.quotientMapOfPresentation.nonempty_iso_of_fiber_iso
      (z.comp F) (y.restrict ψ) e₂ he₂
  refine ⟨pointSpace.mk (⟨L, z⟩ : FieldPoint 𝒜), ?_⟩
  rw [mapPoints_mk]
  exact (pointSpace.mk_eq_mk_of_iso e).trans
    (pointSpace.sound (FieldPoint.equiv_restrict y ψ))

end AlgebraicGeometry.BasedFunctor
