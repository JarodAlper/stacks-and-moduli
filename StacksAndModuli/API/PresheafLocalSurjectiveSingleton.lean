module

public import StacksAndModuli.«Section3.3-Presheaves-and-Sheaves».«part3.3.2-single-map-and-schemes-are-sheaves»
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Singleton refinements of locally surjective maps of presheaves

A locally surjective map is naturally expressed by a covering image sieve.  For
presheaves which are already Zariski sheaves on schemes, the local preimages on a
covering family glue over the coproduct of that family.  This produces one surjective
étale morphism carrying a preimage, without asserting that the coproduct morphism lies
in the original covering sieve.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Opposite ConcreteCategory

universe u

namespace CategoryTheory.Presheaf

variable {F G : AlgebraicGeometry.Scheme.{u}ᵒᵖ ⥤ Type u}

/-- A locally surjective morphism between Zariski sheaves has a preimage after one
surjective étale base change.

The singleton is obtained from a covering family by taking its scheme coproduct and
gluing the local source sections.  In particular, this does not promote membership of
each covering-family arrow in the image sieve to membership of the coproduct arrow;
the latter follows from the newly glued preimage. -/
theorem exists_etale_surjective_lift
    (φ : F ⟶ G)
    (hF : Presieve.IsSheaf AlgebraicGeometry.Scheme.zariskiTopology F)
    (hG : Presieve.IsSheaf AlgebraicGeometry.Scheme.zariskiTopology G)
    [IsLocallySurjective AlgebraicGeometry.Scheme.etaleTopology φ]
    {T : AlgebraicGeometry.Scheme.{u}} (x : G.obj (op T)) :
    ∃ (T' : AlgebraicGeometry.Scheme.{u}) (p : T' ⟶ T),
      AlgebraicGeometry.Etale p ∧ AlgebraicGeometry.Surjective p ∧
        ∃ y : F.obj (op T'), φ.app (op T') y = G.map p.op x := by
  have hR := imageSieve_mem AlgebraicGeometry.Scheme.etaleTopology φ x
  obtain ⟨𝒰, h𝒰⟩ :=
    AlgebraicGeometry.Scheme.exists_cover_of_mem_grothendieckTopology hR
  let T' : AlgebraicGeometry.Scheme.{u} := ∐ 𝒰.X
  let p := Limits.Sigma.desc 𝒰.f
  have hpEtale : AlgebraicGeometry.Etale p := by
    apply AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc
    intro i
    exact 𝒰.map_prop i
  have hpSurjective : AlgebraicGeometry.Surjective p := by
    dsimp [p]
    infer_instance
  have himage (i : 𝒰.I₀) : imageSieve φ x (𝒰.f i) :=
    h𝒰 _ _ ⟨i⟩
  let yᵢ (i : 𝒰.I₀) : F.obj (op (𝒰.X i)) :=
    localPreimage φ x (𝒰.f i) (himage i)
  have hyᵢ (i : 𝒰.I₀) :
      φ.app (op (𝒰.X i)) (yᵢ i) = G.map (𝒰.f i).op x :=
    app_localPreimage φ x (𝒰.f i) (himage i)
  have hbijF := AlgebraicGeometry.bijective_sigma_of_isSheaf_zariskiTopology F hF 𝒰.X
  obtain ⟨y, hy⟩ := hbijF.2 yᵢ
  refine ⟨T', p, hpEtale, hpSurjective, y, ?_⟩
  have hbijG := AlgebraicGeometry.bijective_sigma_of_isSheaf_zariskiTopology G hG 𝒰.X
  apply hbijG.1
  funext i
  change G.map (Sigma.ι 𝒰.X i).op (φ.app (op T') y) =
    G.map (Sigma.ι 𝒰.X i).op (G.map p.op x)
  rw [← NatTrans.naturality_apply φ (Sigma.ι 𝒰.X i).op y]
  have hy' : F.map (Sigma.ι 𝒰.X i).op y = yᵢ i := congrFun hy i
  rw [hy', hyᵢ]
  rw [← types_comp_apply, ← G.map_comp, ← op_comp]
  rw [Sigma.ι_desc]

end CategoryTheory.Presheaf
