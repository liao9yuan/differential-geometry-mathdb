/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.BranchSlideConjugation
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.SlabWedgePush

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set
open scoped _root_.Manifold

namespace OpenPartialHomeomorph
open _root_.OpenPartialHomeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

open _root_.OpenPartialHomeomorph in
theorem disjoint_conjugateMap_images (e : _root_.OpenPartialHomeomorph X Y)
    {f g : Y → Y} (hf : _root_.Set.MapsTo f e.target e.target) (hg : _root_.Set.MapsTo g e.target e.target)
    {A B : Set Y} (hA : A ⊆ e.target) (hB : B ⊆ e.target)
    (hdisj : Disjoint (f '' A) (g '' B)) :
    Disjoint (e.conjugateMap f '' (e.symm '' A))
      (e.conjugateMap g '' (e.symm '' B)) := by
  rw [Set.disjoint_left]
  rintro w ⟨u, ⟨p, hp, rfl⟩, rfl⟩ ⟨v, ⟨q, hq, rfl⟩, heq⟩
  have hps : e.symm p ∈ e.source := e.map_target (hA hp)
  have hqs : e.symm q ∈ e.source := e.map_target (hB hq)
  rw [e.conjugateMap_of_mem _ hps, e.right_inv (hA hp),
    e.conjugateMap_of_mem _ hqs, e.right_inv (hB hq)] at heq
  have hfg : f p = g q := by
    have h := congrArg e heq
    rw [e.right_inv (hg (hB hq)), e.right_inv (hf (hA hp))] at h
    exact h.symm
  exact Set.disjoint_left.mp hdisj ⟨p, hp, rfl⟩ ⟨q, hq, hfg.symm⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OpenPartialHomeomorph.disjoint_conjugateMap_images then
    throwError "Refusing to shadow existing declaration OpenPartialHomeomorph.disjoint_conjugateMap_images"
  Lean.modifyEnv fun env => Lean.addAlias env `OpenPartialHomeomorph.disjoint_conjugateMap_images ``Submission.OpenPartialHomeomorph.disjoint_conjugateMap_images

end OpenPartialHomeomorph

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem mapsTo_of_injective_eqOn_compl {X : Type*} {f : X → X} {C : Set X}
    (hf : Function.Injective f) (hfix : _root_.Set.EqOn f id Cᶜ) : _root_.Set.MapsTo f C C := by
  intro x hx
  by_contra hfx
  have hffx : f (f x) = f x := hfix hfx
  exact hfx ((hf hffx).symm ▸ hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_of_injective_eqOn_compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_of_injective_eqOn_compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_of_injective_eqOn_compl ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mapsTo_of_injective_eqOn_compl

noncomputable def positiveSlabWedgeConjugate {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (c : ℝ) : M → M :=
  E.conjugateMap (e.conjugateMap (positiveWedgePush c))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.positiveSlabWedgeConjugate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.positiveSlabWedgeConjugate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.positiveSlabWedgeConjugate ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.positiveSlabWedgeConjugate

noncomputable def negativeSlabWedgeConjugate {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (c : ℝ) : M → M :=
  E.conjugateMap (e.conjugateMap (negativeWedgePush c))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.negativeSlabWedgeConjugate then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.negativeSlabWedgeConjugate"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.negativeSlabWedgeConjugate ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.negativeSlabWedgeConjugate

def slabWedgeChartSupport {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (c : ℝ) : Set M :=
  E.symm '' (e.symm '' slabWedgeSupport c)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeChartSupport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeChartSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeChartSupport ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeChartSupport

def slabWedgeChartSet {M : Type u} [TopologicalSpace M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (A : Set (ℝ × ℝ × ℝ)) : Set M :=
  E.symm '' (e.symm '' A)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeChartSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeChartSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeChartSet ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slabWedgeChartSet

open _root_.Classical in
theorem slab_wedge_conjugate_properties {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    (E : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3)))
    (hE : E ∈ (plGroupoid 3).maximalAtlas M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 3)) (ℝ × ℝ × ℝ))
    (he : IsPiecewiseAffineOn e e.source) (hei : IsPiecewiseAffineOn e.symm e.target)
    (hesrc : e.source ⊆ E.target) {c : ℝ} {A B : Set (ℝ × ℝ × ℝ)}
    (hsupport : slabWedgeSupport c ⊆ e.target)
    (hAfold : A ⊆ positiveSlabFold c ∩ wedgeSlabInterior c)
    (hBfold : B ⊆ negativeSlabFold c ∩ wedgeSlabInterior c)
    (hAtarget : A ⊆ e.target) (hBtarget : B ⊆ e.target) :
    IsCompact (slabWedgeChartSupport E e c) ∧
      IsPL 3 3 (positiveSlabWedgeConjugate E e c) ∧
      IsPL 3 3 (negativeSlabWedgeConjugate E e c) ∧
      Function.Injective (positiveSlabWedgeConjugate E e c) ∧
      Function.Injective (negativeSlabWedgeConjugate E e c) ∧
      _root_.Set.EqOn (positiveSlabWedgeConjugate E e c) id (slabWedgeChartSupport E e c)ᶜ ∧
      _root_.Set.EqOn (negativeSlabWedgeConjugate E e c) id (slabWedgeChartSupport E e c)ᶜ ∧
      _root_.Set.MapsTo (positiveSlabWedgeConjugate E e c) (slabWedgeChartSupport E e c)
        (slabWedgeChartSupport E e c) ∧
      _root_.Set.MapsTo (negativeSlabWedgeConjugate E e c) (slabWedgeChartSupport E e c)
        (slabWedgeChartSupport E e c) ∧
      Disjoint
        (positiveSlabWedgeConjugate E e c '' slabWedgeChartSet E e A)
        (negativeSlabWedgeConjugate E e c '' slabWedgeChartSet E e B) := by
  let C := slabWedgeSupport c
  let kp := e.conjugateMap (positiveWedgePush c)
  let kn := e.conjugateMap (negativeWedgePush c)
  let K := E.symm '' (e.symm '' C)
  let hp := E.conjugateMap kp
  let hn := E.conjugateMap kn
  have hCcompact : IsCompact C := isCompact_slabWedgeSupport c
  have hposFix : _root_.Set.EqOn (positiveWedgePush c) id Cᶜ :=
    eqOn_positiveWedgePush_id_compl_support c
  have hnegFix : _root_.Set.EqOn (negativeWedgePush c) id Cᶜ :=
    eqOn_negativeWedgePush_id_compl_support c
  have hposInj : Function.Injective (positiveWedgePush c) := by
    intro x y hxy
    exact (positiveWedgePushHomeomorph c).injective (by simpa using hxy)
  have hnegInj : Function.Injective (negativeWedgePush c) := by
    intro x y hxy
    exact (negativeWedgePushHomeomorph c).injective (by simpa using hxy)
  have hposC : _root_.Set.MapsTo (positiveWedgePush c) C C :=
    mapsTo_of_injective_eqOn_compl hposInj hposFix
  have hnegC : _root_.Set.MapsTo (negativeWedgePush c) C C :=
    mapsTo_of_injective_eqOn_compl hnegInj hnegFix
  have hposTarget : _root_.Set.MapsTo (positiveWedgePush c) e.target e.target := by
    intro p hpTarget
    by_cases hpC : p ∈ C
    · exact hsupport (hposC hpC)
    · simpa only [hposFix hpC, id_eq] using hpTarget
  have hnegTarget : _root_.Set.MapsTo (negativeWedgePush c) e.target e.target := by
    intro p hpTarget
    by_cases hpC : p ∈ C
    · exact hsupport (hnegC hpC)
    · simpa only [hnegFix hpC, id_eq] using hpTarget
  have hinnerSupport : e.symm '' C ⊆ E.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact hesrc (e.map_target (hsupport hp))
  have hinnerCompact : IsCompact (e.symm '' C) :=
    hCcompact.image_of_continuousOn (e.continuousOn_symm.mono hsupport)
  have hkpFix : _root_.Set.EqOn kp id (e.symm '' C)ᶜ := e.conjugateMap_eqOn_compl hposFix
  have hknFix : _root_.Set.EqOn kn id (e.symm '' C)ᶜ := e.conjugateMap_eqOn_compl hnegFix
  have hkpTarget : _root_.Set.MapsTo kp E.target E.target := by
    intro p hpTarget
    by_cases hpC : p ∈ e.symm '' C
    · exact hinnerSupport (mapsTo_of_injective_eqOn_compl
        (e.injective_conjugateMap hposInj hposTarget) hkpFix hpC)
    · simpa only [hkpFix hpC, id_eq] using hpTarget
  have hknTarget : _root_.Set.MapsTo kn E.target E.target := by
    intro p hpTarget
    by_cases hpC : p ∈ e.symm '' C
    · exact hinnerSupport (mapsTo_of_injective_eqOn_compl
        (e.injective_conjugateMap hnegInj hnegTarget) hknFix hpC)
    · simpa only [hknFix hpC, id_eq] using hpTarget
  have hkpPL : IsPiecewiseAffineOn kp univ :=
    isPiecewiseAffineOn_conjugateMap e he hei
      ((isPLHomeomorphOn_positiveWedgePush c).isPiecewiseAffineOn.mono e.open_target
        (_root_.Set.subset_univ _)) hposTarget hCcompact hsupport hposFix
  have hknPL : IsPiecewiseAffineOn kn univ :=
    isPiecewiseAffineOn_conjugateMap e he hei
      ((isPLHomeomorphOn_negativeWedgePush c).isPiecewiseAffineOn.mono e.open_target
        (_root_.Set.subset_univ _)) hnegTarget hCcompact hsupport hnegFix
  have hKcompact : IsCompact K :=
    hinnerCompact.image_of_continuousOn (E.continuousOn_symm.mono hinnerSupport)
  have hhpPL : IsPL 3 3 hp :=
    isPL_conjugateMap E hE hkpPL hkpTarget hinnerCompact hinnerSupport hkpFix
  have hhnPL : IsPL 3 3 hn :=
    isPL_conjugateMap E hE hknPL hknTarget hinnerCompact hinnerSupport hknFix
  have hhpInj : Function.Injective hp :=
    E.injective_conjugateMap (e.injective_conjugateMap hposInj hposTarget) hkpTarget
  have hhnInj : Function.Injective hn :=
    E.injective_conjugateMap (e.injective_conjugateMap hnegInj hnegTarget) hknTarget
  have hhpFix : _root_.Set.EqOn hp id Kᶜ := E.conjugateMap_eqOn_compl hkpFix
  have hhnFix : _root_.Set.EqOn hn id Kᶜ := E.conjugateMap_eqOn_compl hknFix
  have hposChart : e.symm '' A ⊆ E.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact hesrc (e.map_target (hAtarget hp))
  have hnegChart : e.symm '' B ⊆ E.target := by
    rintro _ ⟨p, hp, rfl⟩
    exact hesrc (e.map_target (hBtarget hp))
  have hmodelDisj : Disjoint (positiveWedgePush c '' A) (negativeWedgePush c '' B) :=
    disjoint_positive_negative_wedge_push_on_slabInterior.mono
      (_root_.Set.image_mono hAfold) (_root_.Set.image_mono hBfold)
  have hinnerDisj : Disjoint
      (kp '' (e.symm '' A)) (kn '' (e.symm '' B)) :=
    e.disjoint_conjugateMap_images hposTarget hnegTarget hAtarget hBtarget hmodelDisj
  have houterDisj : Disjoint
      (hp '' (E.symm '' (e.symm '' A))) (hn '' (E.symm '' (e.symm '' B))) :=
    E.disjoint_conjugateMap_images hkpTarget hknTarget hposChart hnegChart hinnerDisj
  change IsCompact K ∧ IsPL 3 3 hp ∧ IsPL 3 3 hn ∧ Function.Injective hp ∧
    Function.Injective hn ∧ _root_.Set.EqOn hp id Kᶜ ∧ _root_.Set.EqOn hn id Kᶜ ∧ _root_.Set.MapsTo hp K K ∧
    _root_.Set.MapsTo hn K K ∧ Disjoint
      (hp '' (E.symm '' (e.symm '' A))) (hn '' (E.symm '' (e.symm '' B)))
  exact ⟨hKcompact, hhpPL, hhnPL, hhpInj, hhnInj, hhpFix, hhnFix,
    mapsTo_of_injective_eqOn_compl hhpInj hhpFix,
    mapsTo_of_injective_eqOn_compl hhnInj hhnFix, houterDisj⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.slab_wedge_conjugate_properties then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.slab_wedge_conjugate_properties"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.slab_wedge_conjugate_properties ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.slab_wedge_conjugate_properties

end DifferentialGeometry.Topology.PiecewiseLinear
