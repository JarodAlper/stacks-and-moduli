module

public import StacksAndModuli.API.FiniteProjectiveFiberRank
public import StacksAndModuli.API.SchemeModulesGlobalSectionsIso
public import StacksAndModuli.«Section2.1-Intro».«part2.1.3-projective-space-and-hilbert-quot-functors»

/-!
# Isomorphisms induced on relative projective space

This file records that functoriality of relative projective space sends an
isomorphism of base schemes to an isomorphism.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry

universe u

/-- The map of relative projective spaces induced by the identity of the base
is the identity. -/
@[simp]
theorem AlgebraicGeometry.Scheme.projectiveSpaceOverMap_id
    (n : ℕ) (S : Scheme.{u}) :
    projectiveSpaceOverMap n (𝟙 S) = 𝟙 _ := by
  apply Limits.pullback.hom_ext
  · change projectiveSpaceOverMap n (𝟙 S) ≫
        projectiveSpaceOverπ n S = projectiveSpaceOverπ n S
    rw [projectiveSpaceOverMap_π]
    simp
  · change projectiveSpaceOverMap n (𝟙 S) ≫
        Limits.pullback.snd (specULiftZIsTerminal.from S)
          (specULiftZIsTerminal.from (projectiveSpace n)) =
      Limits.pullback.snd (specULiftZIsTerminal.from S)
        (specULiftZIsTerminal.from (projectiveSpace n))
    exact projectiveSpaceOverMap_absolute_snd n (𝟙 S)

/-- An isomorphism of base schemes induces an isomorphism of their relative
projective spaces. -/
noncomputable def AlgebraicGeometry.Scheme.projectiveSpaceOverMapIso
    (n : ℕ) {S T : Scheme.{u}} (e : T ≅ S) :
    projectiveSpaceOver n T ≅ projectiveSpaceOver n S where
  hom := projectiveSpaceOverMap n e.hom
  inv := projectiveSpaceOverMap n e.inv
  hom_inv_id := by
    rw [projectiveSpaceOverMap_comp, e.hom_inv_id, projectiveSpaceOverMap_id]
  inv_hom_id := by
    rw [projectiveSpaceOverMap_comp, e.inv_hom_id, projectiveSpaceOverMap_id]

namespace AlgebraicGeometry.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The canonical identification of relative projective space over an affine
base with polynomial `Proj` is natural in the coefficient ring. -/
theorem polynomialProjOverSpecIso_hom_naturality
    (n : ℕ) {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (Proj.polynomialProjOverSpecIso (Fin (n + 1)) S).hom ≫
        Proj.polynomialMap (Fin (n + 1)) f =
      Scheme.projectiveSpaceOverMap n
          (Spec.map (CommRingCat.ofHom f)) ≫
        (Proj.polynomialProjOverSpecIso (Fin (n + 1)) R).hom := by
  let eR := Proj.polynomialProjOverSpecIso (Fin (n + 1)) R
  let eS := Proj.polynomialProjOverSpecIso (Fin (n + 1)) S
  apply (cancel_mono eR.inv).mp
  calc
    _ = Scheme.projectiveSpaceOverMap n
          (Spec.map (CommRingCat.ofHom f)) := by
      apply pullback.hom_ext
      · change (eS.hom ≫ Proj.polynomialMap (Fin (n + 1)) f ≫ eR.inv) ≫
            Scheme.projectiveSpaceOverπ n (Spec (.of R)) =
          Scheme.projectiveSpaceOverMap n (Spec.map (CommRingCat.ofHom f)) ≫
            Scheme.projectiveSpaceOverπ n (Spec (.of R))
        rw [Scheme.projectiveSpaceOverMap_π]
        change (eS.hom ≫ Proj.polynomialMap (Fin (n + 1)) f ≫ eR.inv) ≫
              pullback.fst
                (specULiftZIsTerminal.from (Spec (.of R)))
                (specULiftZIsTerminal.from (Proj
                  (MvPolynomial.homogeneousSubmodule
                    (Fin (n + 1)) (ULift.{u} ℤ)))) =
            pullback.fst
                (specULiftZIsTerminal.from (Spec (.of S)))
                (specULiftZIsTerminal.from (Proj
                  (MvPolynomial.homogeneousSubmodule
                    (Fin (n + 1)) (ULift.{u} ℤ)))) ≫
              Spec.map (CommRingCat.ofHom f)
        rw [← Proj.polynomialProjOverSpecIso_hom_toSpec (Fin (n + 1)) R]
        simp only [Category.assoc, eR, Iso.inv_hom_id_assoc]
        rw [Proj.polynomialMap_toSpec]
        rw [← Category.assoc]
        rw [Proj.polynomialProjOverSpecIso_hom_toSpec]
      · change (eS.hom ≫ Proj.polynomialMap (Fin (n + 1)) f ≫ eR.inv) ≫
            pullback.snd _ _ =
          Scheme.projectiveSpaceOverMap n (Spec.map (CommRingCat.ofHom f)) ≫
            pullback.snd _ _
        rw [Scheme.projectiveSpaceOverMap_absolute_snd]
        rw [← Proj.polynomialProjOverSpecIso_hom_polynomialMap (Fin (n + 1)) R]
        simp only [Category.assoc, eR, Iso.inv_hom_id_assoc]
        rw [Proj.polynomialMap_comp]
        rw [Proj.uliftIntCastRingHom_naturality]
        exact Proj.polynomialProjOverSpecIso_hom_polynomialMap (Fin (n + 1)) S
    _ = _ := by
      rw [Category.assoc, eR.hom_inv_id]
      dsimp [Scheme.projectiveSpaceOverMap, Scheme.projectiveSpaceOver,
        Scheme.projectiveSpace]
      simp only [Category.comp_id]

/-- The inverse affine-specialization isomorphisms express the same naturality
square with both maps landing in relative projective space. -/
theorem polynomialMap_comp_polynomialProjOverSpecIso_inv
    (n : ℕ) {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    Proj.polynomialMap (Fin (n + 1)) f ≫
        (Proj.polynomialProjOverSpecIso (Fin (n + 1)) R).inv =
      (Proj.polynomialProjOverSpecIso (Fin (n + 1)) S).inv ≫
        Scheme.projectiveSpaceOverMap n (Spec.map (CommRingCat.ofHom f)) := by
  let eR := Proj.polynomialProjOverSpecIso (Fin (n + 1)) R
  let eS := Proj.polynomialProjOverSpecIso (Fin (n + 1)) S
  apply (Iso.comp_inv_eq eR).mpr
  exact ((Iso.inv_comp_eq eS).mpr
    (polynomialProjOverSpecIso_hom_naturality n f).symm).symm

/-- Pullback of a module along coefficient change on intrinsic polynomial
`Proj` agrees, under the affine-specialization isomorphisms, with pullback along
the Chapter 2 map of relative projective spaces. -/
noncomputable def pullbackPolynomialTransportIso
    (n : ℕ) {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (Q : (Scheme.projectiveSpaceOver n (Spec (.of R))).Modules) :
    (Scheme.Modules.pullback (Proj.polynomialMap (Fin (n + 1)) f)).obj
        ((Scheme.Modules.pullback
          (Proj.polynomialProjOverSpecIso (Fin (n + 1)) R).inv).obj Q) ≅
      (Scheme.Modules.pullback
        (Proj.polynomialProjOverSpecIso (Fin (n + 1)) S).inv).obj
        ((Scheme.Modules.pullback (Scheme.projectiveSpaceOverMap n
          (Spec.map (CommRingCat.ofHom f)))).obj Q) :=
  (Scheme.Modules.pullbackComp
      (Proj.polynomialMap (Fin (n + 1)) f)
      (Proj.polynomialProjOverSpecIso (Fin (n + 1)) R).inv).app Q ≪≫
    (Scheme.Modules.pullbackCongr
      (polynomialMap_comp_polynomialProjOverSpecIso_inv n f)).app Q ≪≫
    ((Scheme.Modules.pullbackComp
      (Proj.polynomialProjOverSpecIso (Fin (n + 1)) S).inv
      (Scheme.projectiveSpaceOverMap n
        (Spec.map (CommRingCat.ofHom f)))).app Q).symm

end AlgebraicGeometry.ProjectiveSpace

namespace AlgebraicGeometry.Scheme

/-- Extension of scalars for global sections, together with the twist
comparison, preserves the Hilbert function under a homomorphism of coefficient
fields. -/
theorem hilbertFunctionOver_pullback_of_globalSectionsBaseChange
    (n : ℕ) {K L : Type u} [Field K] [Field L] (f : K →+* L)
    (Q : (projectiveSpaceOver n (Spec (.of K))).Modules) (d : ℤ)
    (eTwist :
      (Modules.pullback (projectiveSpaceOverMap n
        (Spec.map (CommRingCat.ofHom f)))).obj
          (projectiveSpaceOverTwistModule Q d) ≅
        projectiveSpaceOverTwistModule
          ((Modules.pullback (projectiveSpaceOverMap n
            (Spec.map (CommRingCat.ofHom f)))).obj Q) d)
    (eSections :
      let g := projectiveSpaceOverMap n
        (Spec.map (CommRingCat.ofHom f))
      let Qd := projectiveSpaceOverTwistModule Q d
      let N := (Modules.pullback g).obj Qd
      letI : Algebra K L := f.toAlgebra
      letI : Module K Γ(Qd, ⊤) := Modules.globalSectionsModule
        (projectiveSpaceOverπ n (Spec (.of K))) Qd
      letI : Module L Γ(N, ⊤) := Modules.globalSectionsModule
        (projectiveSpaceOverπ n (Spec (.of L))) N
      L ⊗[K] Γ(Qd, ⊤) ≃ₗ[L] Γ(N, ⊤)) :
    hilbertFunctionOver Q d =
      hilbertFunctionOver
        ((Modules.pullback (projectiveSpaceOverMap n
          (Spec.map (CommRingCat.ofHom f)))).obj Q) d := by
  dsimp only at eSections
  let g := projectiveSpaceOverMap n (Spec.map (CommRingCat.ofHom f))
  let pK := projectiveSpaceOverπ n (Spec (.of K))
  let pL := projectiveSpaceOverπ n (Spec (.of L))
  let Qd := projectiveSpaceOverTwistModule Q d
  let QL := (Modules.pullback g).obj Q
  let N := (Modules.pullback g).obj Qd
  let QLd := projectiveSpaceOverTwistModule QL d
  letI : Algebra K L := f.toAlgebra
  letI : Module K Γ(Qd, ⊤) := Modules.globalSectionsModule pK Qd
  letI : Module L Γ(N, ⊤) := Modules.globalSectionsModule pL N
  letI : Module L Γ(QLd, ⊤) := Modules.globalSectionsModule pL QLd
  let eTwistΓ := Modules.globalSectionsLinearEquivOfIso pL eTwist
  change Module.finrank K Γ(Qd, ⊤) = Module.finrank L Γ(QLd, ⊤)
  calc
    Module.finrank K Γ(Qd, ⊤) = Module.finrank L (L ⊗[K] Γ(Qd, ⊤)) :=
      Module.finrank_baseChange.symm
    _ = Module.finrank L Γ(N, ⊤) := eSections.finrank_eq
    _ = Module.finrank L Γ(QLd, ⊤) := eTwistΓ.finrank_eq

/-- Pullback along a field isomorphism preserves the Hilbert function, provided
pullback is identified with the chosen twist on the transported sheaf. -/
theorem hilbertFunctionOver_pullback_ringIso_of_twistIso
    (n : ℕ) {S K : CommRingCat.{u}}
    (hS : IsField S) (hK : IsField K) (e : S ≅ K)
    (F : (projectiveSpaceOver n (Spec S)).Modules) (d : ℤ)
    (eTwist :
      (Modules.pullback (projectiveSpaceOverMap n (Spec.map e.hom))).obj
          (projectiveSpaceOverTwistModule F d) ≅
        projectiveSpaceOverTwistModule
          ((Modules.pullback (projectiveSpaceOverMap n
            (Spec.map e.hom))).obj F) d) :
    hilbertFunctionOver F d =
      hilbertFunctionOver
        ((Modules.pullback (projectiveSpaceOverMap n
          (Spec.map e.hom))).obj F) d := by
  letI : Field S := hS.toField
  letI : Field K := hK.toField
  let f := projectiveSpaceOverMap n (Spec.map e.hom)
  let pS := projectiveSpaceOverπ n (Spec S)
  let pK := projectiveSpaceOverπ n (Spec K)
  let Fd := projectiveSpaceOverTwistModule F d
  let FK := (Modules.pullback f).obj F
  let FKd := projectiveSpaceOverTwistModule FK d
  letI : IsIso f :=
    (projectiveSpaceOverMapIso n
      (_root_.AlgebraicGeometry.Scheme.Spec.mapIso e.op)).isIso_hom
  letI : Module S Γ(Fd, ⊤) := Modules.globalSectionsModule pS Fd
  letI : Module S Γ(FKd, ⊤) :=
    Modules.globalSectionsModule (f ≫ pS) FKd
  let E := Modules.pullbackGlobalSectionsViaIsoLinearEquiv f pS Fd eTwist
  have hE : Module.finrank S Γ(Fd, ⊤) =
      Module.finrank S Γ(FKd, ⊤) := E.finrank_eq
  change Module.finrank S Γ(Fd, ⊤) = _
  rw [hE]
  letI : Module K Γ(FKd, ⊤) := Modules.globalSectionsModule pK FKd
  letI : Algebra S K := e.hom.hom.toAlgebra
  let modS : Module S Γ(FKd, ⊤) :=
    Module.compHom Γ(FKd, ⊤) e.hom.hom
  have hmod : Modules.globalSectionsModule (f ≫ pS) FKd = modS := by
    unfold Modules.globalSectionsModule modS
    rw [projectiveSpaceOverMap_π, ← Modules.baseRingHom_comp]
  have htransport :
      letI : Module S Γ(FKd, ⊤) := modS
      Module.finrank S Γ(FKd, ⊤) = Module.finrank K Γ(FKd, ⊤) :=
    Module.finrank_compHom_eq_of_ringEquiv e.commRingCatIsoToRingEquiv
  exact (congrArg (fun inst : Module S Γ(FKd, ⊤) ↦
      @Module.finrank S Γ(FKd, ⊤) _ _ inst) hmod).trans htransport

/-- Pullback along an isomorphism of coefficient fields preserves the Hilbert
function. -/
theorem hilbertFunctionOver_pullback_ringIso
    (n : ℕ) {S K : CommRingCat.{u}}
    (hS : IsField S) (hK : IsField K) (e : S ≅ K)
    (F : (projectiveSpaceOver n (Spec S)).Modules) (d : ℤ) :
    hilbertFunctionOver F d =
      hilbertFunctionOver
        ((Modules.pullback (projectiveSpaceOverMap n
          (Spec.map e.hom))).obj F) d := by
  letI : IsIso (Spec.map e.hom) :=
    (_root_.AlgebraicGeometry.Scheme.Spec.mapIso e.op).isIso_hom
  exact hilbertFunctionOver_pullback_ringIso_of_twistIso
    n hS hK e F d
      (projectiveSpaceOverTwistModule_pullbackIso_of_isOpenImmersion
        n (Spec.map e.hom) F d)

/-- A Hilbert-polynomial assertion is preserved by transport along an
isomorphism of coefficient fields. -/
theorem HasHilbertPolynomialOver.pullback_ringIso
    (n : ℕ) {S K : CommRingCat.{u}}
    (hS : IsField S) (hK : IsField K) (e : S ≅ K)
    (F : (projectiveSpaceOver n (Spec S)).Modules)
    (P : Polynomial ℚ) (h : HasHilbertPolynomialOver F P) :
    HasHilbertPolynomialOver
      ((Modules.pullback (projectiveSpaceOverMap n
        (Spec.map e.hom))).obj F) P := by
  filter_upwards [h] with d hd
  rw [← hilbertFunctionOver_pullback_ringIso n hS hK e F]
  exact hd

/-- A Hilbert polynomial over a field propagates to all field-valued points
once global-section dimensions are known to be preserved by every field base
change.  This isolates the formal Hilbert-polynomial step from the geometric
global-sections base-change theorem. -/
theorem HasHilbertPolynomialOver.hasFiberwise_of_hilbertFunctionOver_pullback_eq
    (n : ℕ) {K : CommRingCat.{u}} (_hK : IsField K)
    (Q : (projectiveSpaceOver n (Spec K)).Modules) (P : Polynomial ℚ)
    (hQ : HasHilbertPolynomialOver Q P)
    (hbaseChange : ∀ (L : CommRingCat.{u}) (_hL : IsField L)
      (s : Spec L ⟶ Spec K) (d : ℤ),
      hilbertFunctionOver Q d =
        hilbertFunctionOver
          ((Modules.pullback (projectiveSpaceOverMap n s)).obj Q) d) :
    HasFiberwiseHilbertPolynomial Q P := by
  intro L hL s
  filter_upwards [hQ] with d hd
  rw [← hbaseChange L hL s (d : ℤ)]
  exact hd

/-- A Hilbert polynomial over a field propagates to every field-valued point
when extension of scalars on global sections and pullback of twists are
available for every field extension. -/
theorem HasHilbertPolynomialOver.hasFiberwise_of_globalSectionsBaseChange
    (n : ℕ) {K : Type u} [Field K]
    (Q : (projectiveSpaceOver n (Spec (.of K))).Modules) (P : Polynomial ℚ)
    (hQ : HasHilbertPolynomialOver Q P)
    (eTwist : ∀ (L : Type u) [Field L] (f : K →+* L) (d : ℤ),
      (Modules.pullback (projectiveSpaceOverMap n
        (Spec.map (CommRingCat.ofHom f)))).obj
          (projectiveSpaceOverTwistModule Q d) ≅
        projectiveSpaceOverTwistModule
          ((Modules.pullback (projectiveSpaceOverMap n
            (Spec.map (CommRingCat.ofHom f)))).obj Q) d)
    (eSections : ∀ (L : Type u) [Field L] (f : K →+* L) (d : ℤ),
      let g := projectiveSpaceOverMap n
        (Spec.map (CommRingCat.ofHom f))
      let Qd := projectiveSpaceOverTwistModule Q d
      let N := (Modules.pullback g).obj Qd
      letI : Algebra K L := f.toAlgebra
      letI : Module K Γ(Qd, ⊤) := Modules.globalSectionsModule
        (projectiveSpaceOverπ n (Spec (.of K))) Qd
      letI : Module L Γ(N, ⊤) := Modules.globalSectionsModule
        (projectiveSpaceOverπ n (Spec (.of L))) N
      L ⊗[K] Γ(Qd, ⊤) ≃ₗ[L] Γ(N, ⊤)) :
    HasFiberwiseHilbertPolynomial Q P := by
  apply HasHilbertPolynomialOver.hasFiberwise_of_hilbertFunctionOver_pullback_eq
    n (Field.toIsField K) Q P hQ
  intro L hL s d
  letI : Field L := hL.toField
  obtain ⟨f, rfl⟩ := Spec.map_surjective s
  exact hilbertFunctionOver_pullback_of_globalSectionsBaseChange
    n f.hom Q d (eTwist L f.hom d) (eSections L f.hom d)

/-- It is enough to know twist compatibility and global-sections base change
in natural-number twists: these are exactly the degrees occurring in the
eventual definition of the Hilbert polynomial. -/
theorem HasHilbertPolynomialOver.hasFiberwise_of_naturalDegreeGlobalSectionsBaseChange
    (n : ℕ) {K : Type u} [Field K]
    (Q : (projectiveSpaceOver n (Spec (.of K))).Modules) (P : Polynomial ℚ)
    (hQ : HasHilbertPolynomialOver Q P)
    (eTwist : ∀ (L : Type u) [Field L] (f : K →+* L) (d : ℕ),
      (Modules.pullback (projectiveSpaceOverMap n
        (Spec.map (CommRingCat.ofHom f)))).obj
          (projectiveSpaceOverTwistModule Q (d : ℤ)) ≅
        projectiveSpaceOverTwistModule
          ((Modules.pullback (projectiveSpaceOverMap n
            (Spec.map (CommRingCat.ofHom f)))).obj Q) (d : ℤ))
    (eSections : ∀ (L : Type u) [Field L] (f : K →+* L) (d : ℕ),
      let g := projectiveSpaceOverMap n
        (Spec.map (CommRingCat.ofHom f))
      let Qd := projectiveSpaceOverTwistModule Q (d : ℤ)
      let N := (Modules.pullback g).obj Qd
      letI : Algebra K L := f.toAlgebra
      letI : Module K Γ(Qd, ⊤) := Modules.globalSectionsModule
        (projectiveSpaceOverπ n (Spec (.of K))) Qd
      letI : Module L Γ(N, ⊤) := Modules.globalSectionsModule
        (projectiveSpaceOverπ n (Spec (.of L))) N
      L ⊗[K] Γ(Qd, ⊤) ≃ₗ[L] Γ(N, ⊤)) :
    HasFiberwiseHilbertPolynomial Q P := by
  intro L hL s
  letI : Field L := hL.toField
  obtain ⟨f, rfl⟩ := Spec.map_surjective s
  filter_upwards [hQ] with d hd
  have heq := hilbertFunctionOver_pullback_of_globalSectionsBaseChange
    n f.hom Q (d : ℤ) (eTwist L f.hom d) (eSections L f.hom d)
  have hmap : CommRingCat.ofHom f.hom = f := rfl
  rw [hmap] at heq
  rw [← heq]
  exact hd

/-- A Hilbert polynomial over a field propagates to every field-valued point
once global sections commute with extension of scalars in natural-number
twists.  Compatibility of those twists with pullback is supplied by the
canonical projective-space base-change isomorphism. -/
theorem HasHilbertPolynomialOver.hasFiberwise_of_naturalDegreeGlobalSectionsBaseChange_canonical
    (n : ℕ) {K : Type u} [Field K]
    (Q : (projectiveSpaceOver n (Spec (.of K))).Modules) (P : Polynomial ℚ)
    (hQ : HasHilbertPolynomialOver Q P)
    (eSections : ∀ (L : Type u) [Field L] (f : K →+* L) (d : ℕ),
      let g := projectiveSpaceOverMap n
        (Spec.map (CommRingCat.ofHom f))
      let Qd := projectiveSpaceOverTwistModule Q (d : ℤ)
      let N := (Modules.pullback g).obj Qd
      letI : Algebra K L := f.toAlgebra
      letI : Module K Γ(Qd, ⊤) := Modules.globalSectionsModule
        (projectiveSpaceOverπ n (Spec (.of K))) Qd
      letI : Module L Γ(N, ⊤) := Modules.globalSectionsModule
        (projectiveSpaceOverπ n (Spec (.of L))) N
      L ⊗[K] Γ(Qd, ⊤) ≃ₗ[L] Γ(N, ⊤)) :
    HasFiberwiseHilbertPolynomial Q P := by
  apply HasHilbertPolynomialOver.hasFiberwise_of_naturalDegreeGlobalSectionsBaseChange
    n Q P hQ
  · intro L _ f d
    exact projectiveSpaceOverTwistModule_pullbackIso_nat
      n (Spec.map (CommRingCat.ofHom f)) Q d
  · exact eSections

end AlgebraicGeometry.Scheme

end
