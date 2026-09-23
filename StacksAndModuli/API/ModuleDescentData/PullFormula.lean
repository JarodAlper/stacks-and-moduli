module

public import StacksAndModuli.API.ModuleDescentData.Standard

@[expose] public section

open CategoryTheory Opposite TensorProduct
open scoped ChangeOfRings

universe u

set_option maxHeartbeats 300000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace ModuleCat

lemma pullHom_apply_unit
    {B C T : Type u} [CommRing B] [CommRing C] [CommRing T]
    (l r : B →+* C) (j : C →+* T)
    (N : ModuleCat B)
    (θ : (extendScalars l).obj N ⟶ (extendScalars r).obj N)
    (n : N) :
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := extendScalarsPseudofunctorOpOp)
        (f₁ := (CommRingCat.ofHom l).op) (f₂ := (CommRingCat.ofHom r).op)
        θ (CommRingCat.ofHom j).op (CommRingCat.ofHom (j.comp l)).op
          (CommRingCat.ofHom (j.comp r)).op rfl rfl).hom
        ((1 : T) ⊗ₜ[B,j.comp l] n) =
      (extendScalarsComp r j).inv.app N
        ((1 : T) ⊗ₜ[C,j] (θ ((1 : C) ⊗ₜ[B,l] n))) := by
  unfold Pseudofunctor.LocallyDiscreteOpToCat.pullHom
  change ((extendScalarsComp r j).inv.app N)
      ((extendScalars j).map θ
        ((extendScalarsComp l j).hom.app N ((1 : T) ⊗ₜ[B,j.comp l] n))) = _
  rw [extendScalarsComp_hom_app_one_tmul]
  rw [ExtendScalars.map_tmul]

end ModuleCat
