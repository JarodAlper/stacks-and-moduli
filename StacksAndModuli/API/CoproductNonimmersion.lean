module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# A specialization obstruction to coproduct immersions

An immersion reflects specializations because its underlying map is an embedding.  For a
map out of a coproduct, points in distinct summands cannot specialize to one another.  This
gives a convenient obstruction to a coproduct morphism being an immersion whenever two
different branches acquire a specialization relation in the target.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits Topology

universe v u

namespace AlgebraicGeometry

/-- A coproduct morphism is not an immersion if points in distinct summands map to a
specializing pair. -/
theorem not_isImmersion_sigmaDesc_of_specializes
    {I : Type v} [Small.{u} I] (Z : I → Scheme.{u}) {Y : Scheme.{u}}
    (f : ∀ i, Z i ⟶ Y) {i j : I} (hij : i ≠ j) {x : Z i} {y : Z j}
    (hxy : f i x ⤳ f j y) : ¬ IsImmersion (Sigma.desc f) := by
  intro hf
  have hemb : IsEmbedding (Sigma.desc f) := hf.isEmbedding
  have himage : Sigma.ι Z i x ⤳ Sigma.ι Z j y := by
    apply hemb.isInducing.specializes_iff.mp
    simpa [← Scheme.Hom.comp_apply] using hxy
  have hj : Sigma.ι Z j y ∈ (Sigma.ι Z j).opensRange := ⟨y, rfl⟩
  have hi : Sigma.ι Z i x ∈ (Sigma.ι Z i).opensRange := ⟨x, rfl⟩
  have hi' := himage.mem_open (Sigma.ι Z j).opensRange.isOpen hj
  exact Set.not_nonempty_empty ⟨Sigma.ι Z i x,
    (disjoint_opensRange_sigmaι Z i j hij).le_bot ⟨hi, hi'⟩⟩

end AlgebraicGeometry
