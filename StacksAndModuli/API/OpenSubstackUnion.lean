module

public import StacksAndModuli.API.OpenSubstackLift
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# A union of open substacks is an open substack

Given a family `i : ∀ k, 𝒰 k ⥤ᵇ 𝒳` of open substack inclusions of a prestack **fibered in
groupoids**, the full sub-based-category of `𝒳` on the objects that are *covered* by the
family is an open substack of `𝒳`. This is what
`AlgebraicGeometry.BasedCategory.pointTopology` needs for `isOpen_sUnion`.

Two points are worth recording.

* The naive union — the full subcategory on `∃ k, (i k).fiberEssImage a` — has the right
  *point* set but is **not** an open substack: the objects of `Sch/T` it picks out are
  `{X | ∃ k, range X.hom ⊆ Wₖ}`, and for `T = W₁ ⊔ W₂` disjoint that omits `𝟙_T`, so it is
  not the sieve of any open. The correct property is the covered one, and on field-valued
  points (whose base has one point) the two agree — which is why the point sets match.
* Unlike the intersection (`StacksAndModuli/API/OpenSubstackIntersection.lean`) and the preimage,
  this construction genuinely needs `𝒳.p.IsFiberedInGroupoids`: "covered" has to restrict an
  *object* of `𝒳` to an open of its base, i.e. take a pullback in `𝒳`, and an arbitrary
  `BasedCategory` has none. See the `def:topology-of-stacks` entries in
  `StacksAndModuli/Section4.3-Properties/COMMENTARY.md`.

The property is phrased without mentioning opens at all: `a` is covered when every
field-valued point of its base, lifted to a morphism into `a`, has its source in one of the
`𝒰 k`. That this cuts out exactly the sieve of `⨆ₖ Wₖ` is `coveredProperty_obj_iff`, proved
by comparing the given lift with the canonical one through `g` — both are cartesian because
`𝒳` is fibered in groupoids, so they have canonically isomorphic sources
(`CategoryTheory.Functor.IsFiberedInGroupoids.pullbackDomainUniqueUpToIso`).

## Main results

* `AlgebraicGeometry.coveredProperty` and `AlgebraicGeometry.coveredProperty_obj_iff`
* `AlgebraicGeometry.isOpenSubstackInclusion_restrictι_covered`
* `AlgebraicGeometry.coveredProperty_comp`
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

universe w v₂ u₂ v₃ u₃ u

namespace AlgebraicGeometry

open CategoryTheory Limits CategoryTheory.BasedCategory CategoryTheory.BasedFunctor

variable {𝒳 : BasedCategory.{v₂, u₂} Scheme.{u}}

/-- The object property "locally in the family": every field-valued point of the base of
`a`, lifted to a morphism into `a`, has its source in one of the `𝒰 k`. For a family of
open substacks this says exactly that the base of `a` is covered by the opens over which
`a` restricts into some `𝒰 k`. -/
def coveredProperty {κ : Type w} {𝒰 : κ → BasedCategory.{v₃, u₃} Scheme.{u}}
    (i : ∀ k, 𝒰 k ⥤ᵇ 𝒳) : ObjectProperty 𝒳.obj := fun a =>
  ∀ (K : Type u) (_ : Field K) (h : Spec (CommRingCat.of K) ⟶ 𝒳.p.obj a)
    (b : 𝒳.obj) (φ : b ⟶ a), Functor.IsHomLift 𝒳.p h φ → ∃ k, (i k).fiberEssImage b

variable {κ : Type w} {𝒰 : κ → BasedCategory.{v₃, u₃} Scheme.{u}} (i : ∀ k, 𝒰 k ⥤ᵇ 𝒳)

/-- The covered property is stable under arbitrary isomorphisms, hence fiber-closed. -/
lemma coveredProperty_of_iso {a a' : 𝒳.obj} (e : a ≅ a')
    (h : coveredProperty i a) : coveredProperty i a' := by
  intro K hK f b φ hφ
  haveI := hφ
  refine h K hK (f ≫ 𝒳.p.map e.inv) b (φ ≫ e.inv) ?_
  haveI : Functor.IsHomLift 𝒳.p (𝒳.p.map e.inv) e.inv := inferInstance
  infer_instance

lemma fiberClosed_coveredProperty : FiberClosed (coveredProperty i) :=
  fun _ _ e _ h => coveredProperty_of_iso i e h

variable [𝒳.p.IsFiberedInGroupoids]

/-- **The covered property is cut out by the union of the opens.** -/
lemma coveredProperty_obj_iff (T : Scheme.{u}) (g : overBased T ⥤ᵇ 𝒳) (W : κ → T.Opens)
    (hW : ∀ (k : κ) (Y : Over T), (i k).fiberEssImage (g.obj Y) ↔
      Set.range Y.hom.base ⊆ (W k : Set T)) (X : Over T) :
    coveredProperty i (g.obj X) ↔ Set.range X.hom.base ⊆ ((⨆ k, W k : T.Opens) : Set T) := by
  constructor
  · intro hQ
    rintro t ⟨y, rfl⟩
    haveI h1 : Functor.IsHomLift 𝒳.p (X.left.fromSpecResidueField y)
        (g.map (Over.homMk (X.left.fromSpecResidueField y) rfl :
          (Over.mk (X.left.fromSpecResidueField y ≫ X.hom) : Over T) ⟶ X)) := by
      have hh := CategoryTheory.BasedCategory.basedMap_isHomLift_left T (F := g)
        (Over.homMk (X.left.fromSpecResidueField y) rfl :
          (Over.mk (X.left.fromSpecResidueField y ≫ X.hom) : Over T) ⟶ X)
      simpa using hh
    haveI h2 : Functor.IsHomLift 𝒳.p
        (X.left.fromSpecResidueField y ≫ eqToHom (g.w_obj X).symm)
        (g.map (Over.homMk (X.left.fromSpecResidueField y) rfl :
          (Over.mk (X.left.fromSpecResidueField y ≫ X.hom) : Over T) ⟶ X)) := inferInstance
    obtain ⟨k, hk⟩ := hQ (X.left.residueField y) inferInstance _
      (g.obj (Over.mk (X.left.fromSpecResidueField y ≫ X.hom))) _ h2
    have hr := (hW k (Over.mk (X.left.fromSpecResidueField y ≫ X.hom))).mp hk
    have hy_mem : y ∈ Set.range ((X.left.fromSpecResidueField y).base) := by
      rw [Scheme.range_fromSpecResidueField]
      exact Set.mem_singleton _
    obtain ⟨v, hv⟩ := hy_mem
    have hmem : X.hom.base y ∈ (W k : Set T) := by
      refine hr ⟨v, ?_⟩
      show ((X.left.fromSpecResidueField y) ≫ X.hom).base v = X.hom.base y
      have hcomp : ((X.left.fromSpecResidueField y) ≫ X.hom).base v
          = X.hom.base ((X.left.fromSpecResidueField y).base v) := by simp
      rw [hcomp, hv]
    rw [TopologicalSpace.Opens.coe_iSup]
    exact Set.mem_iUnion.mpr ⟨k, hmem⟩
  · intro hsub K hK h b φ hφ
    haveI := hφ
    haveI hψ1 : Functor.IsHomLift 𝒳.p (h ≫ eqToHom (g.w_obj X))
        (g.map (Over.homMk (h ≫ eqToHom (g.w_obj X)) rfl :
          (Over.mk ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom) : Over T) ⟶ X)) := by
      have hh := CategoryTheory.BasedCategory.basedMap_isHomLift_left T (F := g)
        (Over.homMk (h ≫ eqToHom (g.w_obj X)) rfl :
          (Over.mk ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom) : Over T) ⟶ X)
      simpa using hh
    haveI hψ : Functor.IsHomLift 𝒳.p h
        (g.map (Over.homMk (h ≫ eqToHom (g.w_obj X)) rfl :
          (Over.mk ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom) : Over T) ⟶ X)) := by
      have hinst : Functor.IsHomLift 𝒳.p
          ((h ≫ eqToHom (g.w_obj X)) ≫ eqToHom (g.w_obj X).symm)
          (g.map (Over.homMk (h ≫ eqToHom (g.w_obj X)) rfl :
            (Over.mk ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom) : Over T) ⟶ X)) := inferInstance
      simpa using hinst
    haveI hss : Subsingleton
        ↥((Over.mk ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom) : Over T).left) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum K))
    obtain ⟨k, hk'⟩ : ∃ k, Set.range
        ((Over.mk ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom) : Over T).hom.base)
          ⊆ (W k : Set T) := by
      obtain ⟨pt⟩ : Nonempty ↥(Spec (CommRingCat.of K)) := inferInstance
      have hmem : ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom).base pt
          ∈ ((⨆ k, W k : T.Opens) : Set T) := by
        refine hsub ⟨(h ≫ eqToHom (g.w_obj X)).base pt, ?_⟩
        simp
      rw [TopologicalSpace.Opens.coe_iSup] at hmem
      obtain ⟨k, hk2⟩ := Set.mem_iUnion.mp hmem
      refine ⟨k, ?_⟩
      rintro s ⟨v, rfl⟩
      have hvpt : v = pt := Subsingleton.elim v pt
      subst hvpt
      exact hk2
    refine ⟨k, ?_⟩
    have hbY := (hW k (Over.mk ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom))).mpr hk'
    haveI hεh := CategoryTheory.Functor.IsFiberedInGroupoids.pullbackDomainUniqueUpToIso_hom_isHomLift (p := 𝒳.p) h
      (g.map (Over.homMk (h ≫ eqToHom (g.w_obj X)) rfl :
        (Over.mk ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom) : Over T) ⟶ X)) φ
    haveI hεi := IsHomLift.lift_id_inv 𝒳.p (Spec (CommRingCat.of K))
      (CategoryTheory.Functor.IsFiberedInGroupoids.pullbackDomainUniqueUpToIso (p := 𝒳.p) h
        (g.map (Over.homMk (h ≫ eqToHom (g.w_obj X)) rfl :
          (Over.mk ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom) : Over T) ⟶ X)) φ)
    have hpb : 𝒳.p.obj b = Spec (CommRingCat.of K) := IsHomLift.domain_eq 𝒳.p h φ
    refine BasedFunctor.fiberEssImage_of_iso hbY
      (CategoryTheory.Functor.IsFiberedInGroupoids.pullbackDomainUniqueUpToIso (p := 𝒳.p) h
        (g.map (Over.homMk (h ≫ eqToHom (g.w_obj X)) rfl :
          (Over.mk ((h ≫ eqToHom (g.w_obj X)) ≫ X.hom) : Over T) ⟶ X)) φ).symm ?_
    rw [hpb]
    exact hεi

/-- **A union of open substacks is an open substack.** -/
theorem isOpenSubstackInclusion_restrictι_covered
    [∀ k, BasedFunctor.IsOpenSubstackInclusion (i k)] :
    BasedFunctor.IsOpenSubstackInclusion (𝒳.restrictι (coveredProperty i)) := by
  refine isOpenSubstackInclusion_restrictι _ (fiberClosed_coveredProperty i) (fun T g => ?_)
  choose W hW using fun k => exists_opens_fiberEssImage (i k) T g
  exact ⟨⨆ k, W k, fun X => coveredProperty_obj_iff i T g W hW X⟩

/-- Every value of a morphism factoring through some `i k` satisfies the covered
property. -/
lemma coveredProperty_comp (k : κ) [∀ k, BasedFunctor.IsOpenSubstackInclusion (i k)]
    (T : Scheme.{u}) (F : overBased T ⥤ᵇ 𝒰 k) (Y : Over T) :
    coveredProperty i ((F.comp (i k)).obj Y) := by
  choose W hW using fun k' => exists_opens_fiberEssImage (i k') T (F.comp (i k))
  have hWk : (W k : Set T) = Set.univ := by
    have := (hW k (Over.mk (𝟙 T))).mp
      (fiberEssImage_comp_obj (i k) F (Over.mk (𝟙 T)))
    refine Set.eq_univ_of_univ_subset (subset_trans ?_ this)
    rintro t -
    exact ⟨t, rfl⟩
  refine (coveredProperty_obj_iff i T (F.comp (i k)) W hW Y).mpr ?_
  rw [TopologicalSpace.Opens.coe_iSup]
  intro t _
  exact Set.mem_iUnion.mpr ⟨k, hWk ▸ Set.mem_univ t⟩

end AlgebraicGeometry
