module

public import StacksAndModuli.API.OverPresheafTotal
public import StacksAndModuli.API.PseudofunctorDescentFamilyComposition

/-!
# An affine criterion for stacks without an a priori prestack hypothesis

The ordinary sheaf criterion for the `P`-quasi-compact topology can be applied
to the total presheaf of each morphism presheaf of a pseudofunctor.  This turns
Zariski morphism descent and morphism descent for affine singleton covers into
morphism descent for the whole topology.  Combining this with the effective
descent criterion removes the otherwise extraneous global prestack hypothesis.
-/

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u

namespace AlgebraicGeometry

variable {P : MorphismProperty Scheme.{u}} [P.IsMultiplicative]
  [P.IsStableUnderBaseChange] [IsZariskiLocalAtSource P]
  [(Scheme.propQCTopology P).Subcanonical]

/-- A Zariski stack satisfying descent for every surjective `P`-morphism
between affine schemes is automatically a prestack for the full
`P`-quasi-compact topology. -/
lemma isPrestack_propQCTopology_of_affine_singletons
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{v, w})
    [F.IsStack Scheme.zariskiTopology]
    (hsingle : ∀ {R S : CommRingCat.{u}} (q : R ⟶ S),
      P (Spec.map q) → Surjective (Spec.map q) →
        F.IsStackFor (.singleton (Spec.map q))) :
    F.IsPrestack (Scheme.propQCTopology P) := by
  apply Pseudofunctor.IsPrestack.of_precoverage
      (J := Scheme.propQCPrecoverage P)
  intro B R hR
  obtain ⟨I, X, f, rfl⟩ := R.exists_eq_ofArrows
  rw [← F.IsPrestackFor_generate_iff,
    Pseudofunctor.isPrestackFor_iff_isSheafFor']
  intro S₀ M N a
  let G := F.presheafHom M N
  have hTotalZar : Presieve.IsSheaf Scheme.zariskiTopology
      (PresheafOver.total G) := by
    apply PresheafOver.isSheaf_total Scheme.zariskiTopology G
    exact (isSheaf_iff_isSheaf_of_type _ _).mp
      (Pseudofunctor.IsPrestack.isSheaf Scheme.zariskiTopology M N)
  have hTotalSingleton : ∀ {R S : CommRingCat.{u}} (q : R ⟶ S),
      P (Spec.map q) → Surjective (Spec.map q) →
        Presieve.IsSheafFor (PresheafOver.total G)
          (.singleton (Spec.map q)) := by
    intro R' S' q hq hsurj
    letI : Surjective (Spec.map q) := hsurj
    letI : QuasiCompact (Spec.map q) := by infer_instance
    rw [← Presieve.ofArrows_pUnit.{0}]
    apply PresheafOver.isSheafFor_total_of_lift G
        (fun _ : PUnit.{1} ↦ Spec.map q)
    · simpa only [Presieve.ofArrows_pUnit] using
        (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
          (yoneda.obj S₀)).isSheafFor (.singleton (Spec.map q))
            (Scheme.Hom.generate_singleton_mem_propQCTopology (Spec.map q) hq)
    · intro b
      have hp := (hsingle q hq hsurj).isPrestackFor
      rw [← F.IsPrestackFor_generate_iff,
        Pseudofunctor.isPrestackFor_iff_isSheafFor'] at hp
      rw [Presieve.isSheafFor_iff_generate,
        PresheafOver.generate_lift_eq_overEquiv_symm]
      rw [Sieve.ofArrows, Presieve.ofArrows_pUnit]
      exact hp M N b
  have hTotal : Presieve.IsSheaf (Scheme.propQCTopology P)
      (PresheafOver.total G) :=
    (isSheaf_type_propQCTopology_iff (PresheafOver.total G)).mpr
      ⟨hTotalZar, hTotalSingleton⟩
  rw [← PresheafOver.generate_lift_eq_overEquiv_symm f a,
    ← Presieve.isSheafFor_iff_generate]
  apply PresheafOver.isSheafFor_lift_of_total G f a
  · exact hTotal.isSheafFor _
      (Precoverage.generate_mem_toGrothendieck hR)
  · exact ((GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
      (yoneda.obj S₀)).isSheafFor _
        (Precoverage.generate_mem_toGrothendieck hR)).isSeparatedFor

/-- For a subcanonical `P`-quasi-compact topology, the stack condition is
equivalent to the Zariski stack condition and effective descent for surjective
`P`-morphisms between affine schemes. -/
lemma isStack_propQCTopology_iff_affine_singletons
    (F : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{v, w}) :
    F.IsStack (Scheme.propQCTopology P) ↔
      F.IsStack Scheme.zariskiTopology ∧
        ∀ {R S : CommRingCat.{u}} (q : R ⟶ S),
          P (Spec.map q) → Surjective (Spec.map q) →
            F.IsStackFor (.singleton (Spec.map q)) := by
  constructor
  · intro h
    letI : F.IsStack (Scheme.propQCTopology P) := h
    refine ⟨Pseudofunctor.IsStack.of_le
      (Scheme.zariskiTopology_le_propQCTopology (P := P)), ?_⟩
    intro R S q hq hsurj
    letI : Surjective (Spec.map q) := hsurj
    letI : QuasiCompact (Spec.map q) := by infer_instance
    exact F.isStackFor (.singleton (Spec.map q))
      (Scheme.Hom.generate_singleton_mem_propQCTopology (Spec.map q) hq)
  · rintro ⟨hzar, hsingle⟩
    letI : F.IsStack Scheme.zariskiTopology := hzar
    letI : F.IsPrestack (Scheme.propQCTopology P) :=
      isPrestack_propQCTopology_of_affine_singletons F hsingle
    exact isStack_propQCTopology_of_affine_singletons (P := P) F hsingle

end AlgebraicGeometry
