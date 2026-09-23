module

public import StacksAndModuli.API.FreeStackCompletion
public import StacksAndModuli.API.BasedFunctorLocalEssentialSurjectivity

/-!
# Local density of the free stack completion

The canonical inclusion of a prestack into its free stack completion is locally
essentially surjective.  This is the local half of the stackification property: every
formal object is, after passage to a covering sieve, a cartesian image of an object of
the original prestack.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Functor

universe v u w z

namespace CategoryTheory.BasedCategory.FreeStackCompletion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (X : BasedCategory.{w, z} C) [X.p.IsFiberedInGroupoids]

/-- Local lifts of one well-typed formal object from the original prestack. -/
structure LocalLiftData {base : C} {term : Pre J X} (hterm : IsObj J X term base) where
  sieve : Sieve base
  cover : sieve ∈ J base
  lift : ∀ {T : C} (f : T ⟶ base), sieve f →
    ∃ (x : X.obj) (q : (inclusion J X).obj x ⟶ ⟨base, term, ⟨hterm⟩⟩),
      IsHomLift (proj J X) f q

/-- Every well-typed formal object is locally a cartesian image of an object of the
original prestack. -/
noncomputable def localLiftData {base : C} {term : Pre J X} (hterm : IsObj J X term base) :
    LocalLiftData J X hterm := by
  refine (IsObj.rec (C := C) (J := J) (X := X)
    (motive_1 := fun _ _ h ↦ LocalLiftData J X h)
    (motive_2 := fun _ _ _ _ _ _ _ ↦ PUnit)
    (motive_3 := fun _ _ _ _ _ _ _ _ _ _ ↦ PUnit)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hterm)
  · intro a
    refine ⟨⊤, J.top_mem _, ?_⟩
    intro T f hf
    obtain ⟨b, q, hq⟩ :=
      Functor.IsFiberedInGroupoids.exists_isHomLift (p := X.p) f
    refine ⟨b, (inclusion J X).map q, ?_⟩
    exact BasedFunctor.preserves_isHomLift (inclusion J X) f q
  · intro S T b hb f ih
    obtain ⟨R, hR, hlocal⟩ := ih
    refine ⟨R.pullback f, J.pullback_stable f hR, ?_⟩
    intro T g hg
    obtain ⟨x, q, hq⟩ := hlocal (g ≫ f) hg
    let b : Obj J X := ⟨_, _, ⟨hb⟩⟩
    let a : Obj J X := ⟨_, _, ⟨IsObj.pull hb f⟩⟩
    let raw : RawHom J X a b :=
      ⟨f, .homPullMap _ f, ⟨.pullMap hb f⟩⟩
    let cart : a ⟶ b := ⟦raw⟧
    have : IsHomLift (proj J X) f cart := by
      rw [show f = (proj J X).map cart by
        exact (proj_map_mk J X raw).symm]
      infer_instance
    let : IsHomLift (proj J X) (g ≫ f) q := hq
    let q' : (inclusion J X).obj x ⟶ a :=
      IsStronglyCartesian.map (proj J X) f cart (g := g) (f' := g ≫ f) rfl q
    exact ⟨x, q', inferInstance⟩
  · intro S R Dobj Dmap hDobj hDmap idRel compRel hId hComp ihDobj _ _ _
    let localSieves : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ S⦄, R.1 f → Sieve Y :=
      fun {_} {f} hf ↦ (ihDobj (R.1.arrows.categoryMk f hf)).sieve
    have hlocal : ∀ ⦃Y : C⦄ ⦃f : Y ⟶ S⦄ (hf : R.1 f), localSieves hf ∈ J Y :=
      fun {_} {f} hf ↦ (ihDobj (R.1.arrows.categoryMk f hf)).cover
    refine ⟨Sieve.bind R.1 localSieves, J.bind_covering R.2 hlocal, ?_⟩
    intro Z k hk
    obtain ⟨Y, g, f, hf, hg, hgf⟩ := hk
    let q := R.1.arrows.categoryMk f hf
    obtain ⟨x, eta, heta⟩ := (ihDobj q).lift g hg
    let glued : Obj J X :=
      ⟨_, _, ⟨IsObj.glue R Dobj Dmap hDobj hDmap idRel compRel hId hComp⟩⟩
    let component : Obj J X := ⟨_, Dobj q, ⟨hDobj q⟩⟩
    let raw : RawHom J X component glued :=
      ⟨f, .homGlueMap R Dobj Dmap idRel compRel q,
        ⟨.glueMap R Dobj Dmap idRel compRel
          (.glue R Dobj Dmap hDobj hDmap idRel compRel hId hComp) q⟩⟩
    let epsilon : component ⟶ glued := ⟦raw⟧
    have : IsHomLift (proj J X) g eta := heta
    have : IsHomLift (proj J X) f epsilon := by
      rw [show f = (proj J X).map epsilon by
        exact (proj_map_mk J X raw).symm]
      infer_instance
    have : IsHomLift (proj J X) (g ≫ f) (eta ≫ epsilon) := inferInstance
    exact ⟨x, eta ≫ epsilon, hgf ▸ inferInstance⟩
  all_goals (intros; exact PUnit.unit)

/-- The inclusion of a prestack into its free stack completion is locally essentially
surjective. -/
theorem inclusion_isLocallyEssentiallySurjective :
    BasedFunctor.IsLocallyEssentiallySurjective (J := J) (inclusion J X) := by
  rintro ⟨base, term, valid⟩
  let hterm := Classical.choice valid
  let data := localLiftData J X hterm
  refine ⟨data.sieve, data.cover, ?_⟩
  intro T f hf
  obtain ⟨x, q, hq⟩ := data.lift f hf
  exact ⟨x, q, hq⟩

end CategoryTheory.BasedCategory.FreeStackCompletion
