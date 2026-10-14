/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Submission.DifferentialGeometry.Topology.LocalDegree.Relative
import Submission.DifferentialGeometry.Topology.InvarianceOfDomainManifold

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Set _root_.Metric
open scoped _root_.Topology

namespace DifferentialGeometry.LocalDegree

open _root_.Submission.DifferentialGeometry.Homology

variable {d : ℕ}

theorem exists_relativeHomologyIso_of_isolatingRadius_injOn
    {f : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    {x : EuclideanSpace ℝ (Fin (d + 1))} {R : ℝ}
    (hR : IsolatingRadius f x R) (hinj : _root_.Set.InjOn f (_root_.Metric.ball x R)) :
    ∃ i : relativeHomology (TopCat.of (_root_.Metric.ball x R))
        ({(⟨x, _root_.Metric.mem_ball_self hR.pos⟩ : _root_.Metric.ball x R)}ᶜ : Set (_root_.Metric.ball x R))
        (ModuleCat.of ℤ ℤ) (d + 1) ≅
      relativeHomology (TopCat.of (EuclideanSpace ℝ (Fin (d + 1))))
        ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (d + 1))))
        (ModuleCat.of ℤ ℤ) (d + 1),
      i.hom = hR.relativeHomologyMap (ModuleCat.of ℤ ℤ) (d + 1) := by
  classical
  let B : Set (EuclideanSpace ℝ (Fin (d + 1))) := _root_.Metric.ball x R
  let V : Set (EuclideanSpace ℝ (Fin (d + 1))) := f '' B
  have hBopen : IsOpen B := _root_.Metric.isOpen_ball
  have hfB : ContinuousOn f B := hR.continuousOn.mono _root_.Metric.ball_subset_closedBall
  have hVopen : IsOpen V :=
    DifferentialGeometry.Topology.invariance_of_domain_isOpen_image hBopen hfB hinj
  have hxB : x ∈ B := _root_.Metric.mem_ball_self hR.pos
  have hfx : f x = 0 := (hR.zero_iff x (_root_.Metric.mem_closedBall_self hR.pos.le)).2 rfl
  have hzV : (0 : EuclideanSpace ℝ (Fin (d + 1))) ∈ V := ⟨x, hxB, hfx⟩
  let g : B → EuclideanSpace ℝ (Fin (d + 1)) := B.domRestrict f
  have hgcont : Continuous g := hfB.domRestrict
  have hginj : Function.Injective g := fun a b hab => Subtype.ext (hinj a.2 b.2 hab)
  have hgopen : IsOpenMap g := by
    intro W hW
    have hWopen : IsOpen ((Subtype.val : B → EuclideanSpace ℝ (Fin (d + 1))) '' W) :=
      hBopen.isOpenMap_subtype_val W hW
    have hWB : ((Subtype.val : B → EuclideanSpace ℝ (Fin (d + 1))) '' W) ⊆ B :=
      fun _ ⟨a, _, ha⟩ => ha ▸ a.2
    have himg : g '' W = f '' ((Subtype.val : B → EuclideanSpace ℝ (Fin (d + 1))) '' W) := by
      rw [← _root_.Set.image_comp]
      rfl
    rw [himg]
    exact DifferentialGeometry.Topology.invariance_of_domain_isOpen_image hWopen
      (hfB.mono hWB) (hinj.mono hWB)
  have hge : Topology.IsOpenEmbedding g :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hgcont hginj hgopen
  have hrange : Set.range g = V := by
    ext z
    simp only [Set.mem_range]
    exact ⟨fun ⟨a, ha⟩ => ⟨a.1, a.2, ha⟩,
      fun ⟨a, ha, haz⟩ => ⟨⟨a, ha⟩, haz⟩⟩
  let e : B ≃ₜ V := hge.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  have he_apply (a : B) : (e a : EuclideanSpace ℝ (Fin (d + 1))) = f a := rfl
  have he_zero : e ⟨x, hxB⟩ = ⟨0, hzV⟩ := Subtype.ext (he_apply _ |>.trans hfx)
  have he : ∀ a : B,
      a ∈ ({(⟨x, hxB⟩ : B)}ᶜ : Set B) ↔
        e a ∈ ({(⟨0, hzV⟩ : V)}ᶜ : Set V) := by
    intro a
    change a ≠ ⟨x, hxB⟩ ↔ e a ≠ ⟨0, hzV⟩
    rw [← he_zero]
    exact (not_congr e.injective.eq_iff).symm
  let i₁ : relativeHomology (TopCat.of B) ({(⟨x, hxB⟩ : B)}ᶜ : Set B)
      (ModuleCat.of ℤ ℤ) (d + 1) ≅
      relativeHomology (TopCat.of V) ({(⟨0, hzV⟩ : V)}ᶜ : Set V)
        (ModuleCat.of ℤ ℤ) (d + 1) :=
    relativeHomologyIso (X := TopCat.of B) (Y := TopCat.of V)
      (s := ({(⟨x, hxB⟩ : B)}ᶜ : Set B))
      (t := ({(⟨0, hzV⟩ : V)}ᶜ : Set V)) (ModuleCat.of ℤ ℤ) e he (d + 1)
  let i₂ := puncturedNeighborhoodHomologyIso
    (TopCat.of (EuclideanSpace ℝ (Fin (d + 1)))) V 0 hzV
      (ModuleCat.of ℤ ℤ) hVopen (d + 1)
  refine ⟨i₁ ≪≫ i₂, ?_⟩
  change i₁.hom ≫ i₂.hom = hR.relativeHomologyMap (ModuleCat.of ℤ ℤ) (d + 1)
  erw [relativeHomologyIso_hom, puncturedNeighborhoodHomologyIso_hom]
  erw [← relativeHomologyMap_comp]
  rw [hR.relativeHomologyMap_eq]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.LocalDegree.exists_relativeHomologyIso_of_isolatingRadius_injOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.LocalDegree.exists_relativeHomologyIso_of_isolatingRadius_injOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.LocalDegree.exists_relativeHomologyIso_of_isolatingRadius_injOn ``Submission.DifferentialGeometry.LocalDegree.exists_relativeHomologyIso_of_isolatingRadius_injOn

end DifferentialGeometry.LocalDegree
