module

public import StacksAndModuli.«Section3.5-Stacks».«part3.5.1-the-definition»
public import StacksAndModuli.«Section3.4-Prestacks».«part3.4.2a-action-quotient-prestacks»

/-!
# Morphism descent for action quotient prestacks

This file supplies the reusable morphism-descent half of the stack argument for an
action quotient prestack.  Object descent for the principal-bundle quotient stack is
strictly stronger and requires a torsor/principal-bundle API.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Functor Opposite

universe w v u

namespace CategoryTheory.PresheafAction

variable {C : Type u} [Category.{v} C] (A : PresheafAction.{w} C)

/-- If the acting group presheaf and the acted-on presheaf are sheaves, morphisms in
the action quotient prestack glue uniquely. -/
theorem quotientProj_morphismsGlue_of_sheaves (J : GrothendieckTopology C)
    (hG : Presieve.IsSheaf J (A.G ⋙ forget GrpCat))
    (hU : Presieve.IsSheaf J A.U) :
    A.quotientProj.MorphismsGlue J := by
  intro S R hR a b ha hb φ hφlift hφcompat
  rcases a with ⟨abase, apoint⟩
  rcases b with ⟨bbase, bpoint⟩
  dsimp [quotientProj] at ha hb
  subst S
  subst bbase
  let pullObj : ∀ {T : C}, (T ⟶ abase) → A.QuotientObj := fun {T} g ↦
    { base := T
      point := A.U.map g.op apoint }
  let pullHom : ∀ {T : C} (g : T ⟶ abase), A.QuotientHom (pullObj g)
      { base := abase, point := apoint } := fun {T} g ↦
    { base := g
      gauge := 1
      relation := by
        letI := A.action (op T)
        simp [pullObj] }
  have pullHom_lift : ∀ {T : C} (g : T ⟶ abase),
      A.quotientProj.IsHomLift g (pullHom g) := by
    intro T g
    exact Functor.IsHomLift.map (p := A.quotientProj) (pullHom g)
  let restrictHom : ∀ {T Z : C} (f : T ⟶ abase) (g : Z ⟶ T),
      A.QuotientHom (pullObj (g ≫ f)) (pullObj f) := fun {T Z} f g ↦
    { base := g
      gauge := 1
      relation := by
        letI := A.action (op Z)
        simpa [pullObj] using congrArg (fun q ↦ q apoint) (A.U.map_comp f.op g.op) }
  have restrictHom_lift : ∀ {T Z : C} (f : T ⟶ abase) (g : Z ⟶ T),
      A.quotientProj.IsHomLift g (restrictHom f g) := by
    intro T Z f g
    exact Functor.IsHomLift.map (p := A.quotientProj) (restrictHom f g)
  have restrictHom_comp_pullHom : ∀ {T Z : C} (f : T ⟶ abase) (g : Z ⟶ T),
      QuotientHom.comp A (restrictHom f g) (pullHom f) = pullHom (g ≫ f) := by
    intro T Z f g
    apply QuotientHom.ext <;> simp [restrictHom, pullHom]
  let fam : Presieve.FamilyOfElements (A.G ⋙ forget GrpCat) R.arrows :=
    fun T g hg ↦ (φ hg (pullHom g) (pullHom_lift g)).gauge
  have fam_compatible : fam.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro T Z f g hf
    have hsame := restrictHom_comp_pullHom f g
    have hcompLift : A.quotientProj.IsHomLift (g ≫ f)
        (QuotientHom.comp A (restrictHom f g) (pullHom f)) := by
      letI := restrictHom_lift f g
      letI := pullHom_lift f
      exact IsHomLift.comp (p := A.quotientProj) g f (restrictHom f g) (pullHom f)
    let Lifted := { q : A.QuotientHom (pullObj (g ≫ f))
        { base := abase, point := apoint } //
          A.quotientProj.IsHomLift (g ≫ f) q }
    have hpairs :
        (⟨QuotientHom.comp A (restrictHom f g) (pullHom f), hcompLift⟩ : Lifted) =
          ⟨pullHom (g ≫ f), pullHom_lift (g ≫ f)⟩ := by
      apply Subtype.ext
      exact hsame
    have hφsame := congrArg
      (fun q : Lifted ↦ φ (R.downward_closed hf g) q.1 q.2) hpairs
    have hcomp := hφcompat hf (restrictHom f g) (pullHom f)
      (pullHom_lift f) (restrictHom_lift f g)
    change φ _ (QuotientHom.comp A (restrictHom f g) (pullHom f)) _ =
      QuotientHom.comp A (restrictHom f g) (φ hf (pullHom f) _) at hcomp
    have htotal : φ (R.downward_closed hf g) (pullHom (g ≫ f))
        (pullHom_lift (g ≫ f)) =
          QuotientHom.comp A (restrictHom f g) (φ hf (pullHom f) (pullHom_lift f)) :=
      hφsame.symm.trans (by simpa only using hcomp)
    have hgauge := congrArg QuotientHom.gauge htotal
    simpa [fam, restrictHom, QuotientHom.comp] using hgauge
  obtain ⟨gauge, hgauge, hgauge_unique⟩ := (hG R hR) fam fam_compatible
  change A.G.obj (op abase) at gauge
  letI := A.action (op abase)
  have global_relation : A.U.map (𝟙 abase).op bpoint = gauge • apoint := by
    refine ((hU R hR).isSeparatedFor).ext ?_
    intro T g hg
    let theta := φ hg (pullHom g) (pullHom_lift g)
    have htheta_lift := hφlift hg (pullHom g) (pullHom_lift g)
    let baseg : A.quotientProj.obj (pullObj g) ⟶
        A.quotientProj.obj { base := abase, point := bpoint } := g
    have htheta_lift' : A.quotientProj.IsHomLift baseg theta := by
      change A.quotientProj.IsHomLift g theta
      exact htheta_lift
    letI := htheta_lift'
    have hbase : baseg = theta.base :=
      IsHomLift.eq_of_isHomLift A.quotientProj baseg theta
    change g = theta.base at hbase
    letI := A.action (op T)
    have hmapbase : A.U.map g.op bpoint = A.U.map theta.base.op bpoint :=
      congrArg (fun k ↦ A.U.map k.op bpoint) hbase
    have hgam : A.G.map g.op gauge = theta.gauge := by
      simpa [fam, theta] using hgauge g hg
    calc
      A.U.map g.op (A.U.map (𝟙 abase).op bpoint) = A.U.map g.op bpoint := by simp
      _ = theta.gauge • A.U.map g.op apoint :=
        hmapbase.trans (by simpa [pullObj] using theta.relation)
      _ = A.G.map g.op gauge • A.U.map g.op apoint :=
        congrArg (fun k ↦ k • A.U.map g.op apoint) hgam.symm
      _ = A.U.map g.op (gauge • apoint) :=
        (A.map_smul g.op gauge apoint).symm
  let Phi : A.QuotientHom { base := abase, point := apoint }
      { base := abase, point := bpoint } :=
    { base := 𝟙 abase
      gauge := gauge
      relation := global_relation }
  have Phi_lift : A.quotientProj.IsHomLift (𝟙 abase) Phi :=
    Functor.IsHomLift.map (p := A.quotientProj) Phi
  refine ⟨Phi, ⟨Phi_lift, ?_⟩, ?_⟩
  · intro T g hg x xi hxi
    letI := hxi
    letI := pullHom_lift g
    letI : IsStronglyCartesian A.quotientProj g (pullHom g) :=
      Functor.IsFiberedInGroupoids.isStronglyCartesian_of_isHomLift
        A.quotientProj g (pullHom g)
    let chi : A.QuotientHom x (pullObj g) :=
      IsStronglyCartesian.map A.quotientProj g (pullHom g)
        (Category.id_comp g).symm xi
    have hchi_fac : QuotientHom.comp A chi (pullHom g) = xi :=
      IsStronglyCartesian.fac A.quotientProj g (pullHom g)
        (Category.id_comp g).symm xi
    have hchi_lift : A.quotientProj.IsHomLift (𝟙 T) chi := by
      simpa [chi] using IsStronglyCartesian.map_isHomLift A.quotientProj g
        (pullHom g) (Category.id_comp g).symm xi
    let theta := φ hg (pullHom g) (pullHom_lift g)
    have htheta_lift := hφlift hg (pullHom g) (pullHom_lift g)
    let baseg : A.quotientProj.obj (pullObj g) ⟶
        A.quotientProj.obj { base := abase, point := bpoint } := g
    have htheta_lift' : A.quotientProj.IsHomLift baseg theta := by
      change A.quotientProj.IsHomLift g theta
      exact htheta_lift
    letI := htheta_lift'
    have htheta_base : g = theta.base := by
      have h := IsHomLift.eq_of_isHomLift A.quotientProj baseg theta
      change g = theta.base at h
      exact h
    have htheta_gauge : theta.gauge = A.G.map g.op gauge := by
      simpa [fam, theta] using (hgauge g hg).symm
    have theta_eq : theta = QuotientHom.comp A (pullHom g) Phi := by
      apply QuotientHom.ext
      · simpa [Phi] using htheta_base.symm
      · simpa [Phi, pullHom] using htheta_gauge
    have hcompLift : A.quotientProj.IsHomLift g
        (QuotientHom.comp A chi (pullHom g)) := by
      letI := hchi_lift
      letI := pullHom_lift g
      change A.quotientProj.IsHomLift g (chi ≫ pullHom g)
      simpa only [Category.id_comp] using
        IsHomLift.comp (p := A.quotientProj) (𝟙 T) g chi (pullHom g)
    let Lifted := { q : A.QuotientHom x { base := abase, point := apoint } //
      A.quotientProj.IsHomLift g q }
    have hpairs :
        (⟨QuotientHom.comp A chi (pullHom g), hcompLift⟩ : Lifted) = ⟨xi, hxi⟩ := by
      apply Subtype.ext
      exact hchi_fac
    have hφsame := congrArg (fun q : Lifted ↦ φ hg q.1 q.2) hpairs
    have hcompat := hφcompat hg chi (pullHom g) (pullHom_lift g) hchi_lift
    simp only [Category.id_comp] at hcompat
    change φ _ (QuotientHom.comp A chi (pullHom g)) _ =
      QuotientHom.comp A chi theta at hcompat
    have hcompat' : φ hg (QuotientHom.comp A chi (pullHom g)) hcompLift =
        QuotientHom.comp A chi theta := by
      convert hcompat using 1
    have hfirst : φ hg xi hxi = QuotientHom.comp A chi theta :=
      hφsame.symm.trans hcompat'
    calc
      φ hg xi hxi = QuotientHom.comp A chi theta := hfirst
      _ = QuotientHom.comp A chi (QuotientHom.comp A (pullHom g) Phi) := by
        rw [theta_eq]
      _ = QuotientHom.comp A (QuotientHom.comp A chi (pullHom g)) Phi := by
        apply QuotientHom.ext <;>
          simp [QuotientHom.comp, mul_assoc, Functor.map_comp]
      _ = QuotientHom.comp A xi Phi := by rw [hchi_fac]
  · intro Psi hPsi
    apply QuotientHom.ext
    · let baseid : A.quotientProj.obj { base := abase, point := apoint } ⟶
          A.quotientProj.obj { base := abase, point := bpoint } := 𝟙 abase
      have hPsi_lift' : A.quotientProj.IsHomLift baseid Psi := by
        change A.quotientProj.IsHomLift (𝟙 abase) Psi
        exact hPsi.1
      letI := hPsi_lift'
      have hbase := IsHomLift.eq_of_isHomLift A.quotientProj baseid Psi
      change (𝟙 abase) = Psi.base at hbase
      simpa [Phi] using hbase.symm
    · change Psi.gauge = gauge
      apply hgauge_unique
      intro T g hg
      have hfactor := hPsi.2 hg (pullHom g) (pullHom_lift g)
      change φ hg (pullHom g) _ = QuotientHom.comp A (pullHom g) Psi at hfactor
      have hfactor_gauge := congrArg QuotientHom.gauge hfactor
      simpa [fam, pullHom, QuotientHom.comp] using hfactor_gauge.symm

end CategoryTheory.PresheafAction
