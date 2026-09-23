module

public import StacksAndModuli.API.BasedFunctorLocalEssentialSurjectivity
public import StacksAndModuli.API.SchemeRepresentableSheafDescent
public import StacksAndModuli.API.StackPresentationLocalLift

/-!
# Local essential surjectivity of a smooth presentation

A morphism from a scheme representable with smooth surjective fibres is locally
essentially surjective on the big étale site.  This is the object-level local lifting
input used by generalized Yoneda descent.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor
open CategoryTheory.BasedCategory

universe v uₓ u

namespace AlgebraicGeometry.BasedFunctor

/-- A smooth surjective presentation by a scheme is locally essentially surjective for
the big étale topology. -/
theorem RepresentableWith.isLocallyEssentiallySurjective_etale
    {X : BasedCategory.{v, uₓ} Scheme.{u}} [X.p.IsFiberedInGroupoids]
    {U : Scheme.{u}}
    (q : BasedFunctor (overBased U) X)
    (hq : RepresentableWith
      (@_root_.AlgebraicGeometry.Surjective ⊓ @_root_.AlgebraicGeometry.Smooth :
        MorphismProperty Scheme.{u}) q) :
    q.IsLocallyEssentiallySurjective (J := Scheme.etaleTopology) := by
  classical
  intro y
  let S := X.p.obj y
  let gy : BasedFunctor (overBased S) X :=
    twoYonedaPullback S (⟨y, rfl⟩ : X.p.Fiber S)
  obtain ⟨S', p, hpEtale, hpSurjective, lift, ⟨e⟩⟩ :=
    hq.exists_etale_surjective_lift gy
  let _ : Etale p := hpEtale
  let _ : Surjective p := hpSurjective
  let R : Sieve S := Sieve.generateSingleton p
  refine ⟨R, ?_, ?_⟩
  · change R ∈ Scheme.etaleTopology S
    rw [show R = Sieve.generateSingleton p from rfl,
      ← Sieve.generateSingleton_eq]
    exact Scheme.generate_singleton_mem_etaleTopology_of_smooth p
  · intro T f hf
    obtain ⟨h, rfl⟩ := hf
    let z : Over S' := Over.mk h
    let π : gy.obj ((overBased.map p).obj z) ⟶ y :=
      IsPreFibered.pullbackMap (p := X.p) rfl (((overBased.map p).obj z).hom)
    let ell : q.obj (lift.obj z) ⟶ y := e.hom.toNatTrans.app z ≫ π
    refine ⟨lift.obj z, ell, ?_⟩
    haveI he : IsHomLift X.p (𝟙 T) (e.hom.toNatTrans.app z) :=
      e.hom.isHomLift (show (overBased S').p.obj z = T from rfl)
    haveI hπ : IsHomLift X.p (((overBased.map p).obj z).hom) π := inferInstance
    have hcomp : IsHomLift X.p
        ((𝟙 T) ≫ ((overBased.map p).obj z).hom) ell := inferInstance
    simpa [z, overBased.map] using hcomp

end AlgebraicGeometry.BasedFunctor
