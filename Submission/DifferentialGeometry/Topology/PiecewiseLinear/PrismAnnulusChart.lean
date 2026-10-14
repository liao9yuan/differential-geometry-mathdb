/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Submission.DifferentialGeometry.Topology.Manifold.RoundedCylinder
import Submission.DifferentialGeometry.Topology.Simplex.NormedBall
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.PLBallSphere

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Metric _root_.Topology
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Submission.DifferentialGeometry.Manifold

noncomputable def prismBallHomeomorph :
    (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) ≃ₜ
      (_root_.Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 × _root_.Set.Icc (0 : ℝ) 1) :=
  (_root_.Homeomorph.Set.prod _ _).trans
    (_root_.Homeomorph.prodCongr
      (DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph
        (EuclideanSpace.equiv (Fin 2) ℝ).symm) (_root_.Homeomorph.refl _))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prismBallHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prismBallHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prismBallHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prismBallHomeomorph

theorem prismBallHomeomorph_mem_sphere_iff
    (p : (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ))) :
    (prismBallHomeomorph p).1.val ∈ _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ↔
      p.val.1 ∈ stdSimplexBoundary 2 := by
  have h := DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph_mem_sphere_iff
    (EuclideanSpace.equiv (Fin 2) ℝ).symm ⟨p.val.1, p.property.1⟩
  exact h.trans ⟨fun hp => ⟨p.property.1, hp⟩, fun hp => hp.2⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prismBallHomeomorph_mem_sphere_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prismBallHomeomorph_mem_sphere_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prismBallHomeomorph_mem_sphere_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prismBallHomeomorph_mem_sphere_iff

noncomputable def prismAnnulusSource : TopologicalSpace.Opens
    (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)) where
  carrier := prismBallHomeomorph ⁻¹' ballPrismCollar (EuclideanSpace ℝ (Fin 2))
  is_open' := (ballPrismCollar _).isOpen.preimage prismBallHomeomorph.continuous

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusSource ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusSource

noncomputable def prismAnnulusHomeomorph :
    prismAnnulusSource ≃ₜ ballPrismCollar (EuclideanSpace ℝ (Fin 2)) :=
  prismBallHomeomorph.subtype (fun _ => Iff.rfl)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusHomeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusHomeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusHomeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusHomeomorph

theorem mem_prismAnnulusSource_of_boundary
    (p : (stdSimplex ℝ (Fin 3) ×ˢ _root_.Set.Icc (0 : ℝ) 1 : Set ((Fin 3 → ℝ) × ℝ)))
    (hp : p.val.1 ∈ stdSimplexBoundary 2) : p ∈ prismAnnulusSource := by
  have hn := mem_sphere_zero_iff_norm.mp ((prismBallHomeomorph_mem_sphere_iff p).mpr hp)
  change (prismBallHomeomorph p).1.val ≠ 0
  intro heq
  rw [heq, norm_zero] at hn
  norm_num at hn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.mem_prismAnnulusSource_of_boundary then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.mem_prismAnnulusSource_of_boundary"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.mem_prismAnnulusSource_of_boundary ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.mem_prismAnnulusSource_of_boundary

@[instance_reducible]
noncomputable def prismAnnulusChartedSpace :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 2))
      prismAnnulusSource := by
  let _ := ballPrismCollarChartedSpace 1
  exact DifferentialGeometry.Manifold.Homeomorph.pullbackChartedSpace prismAnnulusHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChartedSpace ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChartedSpace

theorem prismAnnulus_isManifold :
    let _ := prismAnnulusChartedSpace
    IsManifold ((𝓡 1).prod (𝓡∂ 2)) ∞ prismAnnulusSource := by
  let _ := ballPrismCollarChartedSpace 1
  let _ : IsManifold ((𝓡 1).prod (𝓡∂ 2)) ∞
      (ballPrismCollar (EuclideanSpace ℝ (Fin 2))) := ballPrismCollar_isManifold 1
  exact DifferentialGeometry.Manifold.Homeomorph.instIsManifoldPullback prismAnnulusHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulus_isManifold then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulus_isManifold"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulus_isManifold ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulus_isManifold

noncomputable def prismAnnulusDiffeomorph :
    let _ := ballPrismCollarChartedSpace 1
    let _ := prismAnnulusChartedSpace
    Diffeomorph ((𝓡 1).prod (𝓡∂ 2)) ((𝓡 1).prod (𝓡∂ 2))
      prismAnnulusSource (ballPrismCollar (EuclideanSpace ℝ (Fin 2))) ∞ := by
  let _ := ballPrismCollarChartedSpace 1
  let _ : IsManifold ((𝓡 1).prod (𝓡∂ 2)) ∞
      (ballPrismCollar (EuclideanSpace ℝ (Fin 2))) := ballPrismCollar_isManifold 1
  exact DifferentialGeometry.Manifold.Homeomorph.pullbackDiffeomorph prismAnnulusHomeomorph

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusDiffeomorph ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusDiffeomorph

theorem prismAnnulus_boundary_iff (p : prismAnnulusSource) :
    let _ := prismAnnulusChartedSpace
    p ∈ ((𝓡 1).prod (𝓡∂ 2)).boundary prismAnnulusSource ↔
      p.val.val.1 ∈ stdSimplexBoundary 2 ∨ p.val.val.2 = 0 ∨ p.val.val.2 = 1 := by
  let _ := ballPrismCollarChartedSpace 1
  let _ := prismAnnulusChartedSpace
  dsimp only
  rw [← prismAnnulusDiffeomorph.preimage_boundary (by simp)]
  change prismAnnulusHomeomorph p ∈ ((𝓡 1).prod (𝓡∂ 2)).boundary
    (ballPrismCollar (EuclideanSpace ℝ (Fin 2))) ↔ _
  have hb := ballPrismCollar_boundary_iff 1 (prismAnnulusHomeomorph p)
  dsimp only at hb
  rw [hb]
  exact or_congr (prismBallHomeomorph_mem_sphere_iff p.val) Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulus_boundary_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulus_boundary_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulus_boundary_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulus_boundary_iff

noncomputable def prismAnnulusChart
    (v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (upper : Bool) :
    OpenPartialHomeomorph prismAnnulusSource
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 2)) :=
  prismAnnulusHomeomorph.toOpenPartialHomeomorph.trans (ballPrismCollarChart 1 v upper)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart

theorem prismAnnulusChart_mem_atlas
    (v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (upper : Bool) :
    let _ := prismAnnulusChartedSpace
    prismAnnulusChart v upper ∈
      atlas (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanHalfSpace 2)) prismAnnulusSource :=
  ⟨_, ballPrismCollarChart_mem_atlas 1 v upper, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_mem_atlas then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_mem_atlas"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_mem_atlas ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_mem_atlas

theorem prismAnnulusChart_mem_source_iff
    (v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (i : Bool) (p : prismAnnulusSource) :
    p ∈ (prismAnnulusChart v i).source ↔
      ((ballPrismCollarHomeomorph _).symm (prismAnnulusHomeomorph p)).1 ≠ -v ∧
        if i then 0 < p.val.val.2 else p.val.val.2 < 1 := by
  let _ : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 1 + 1) := ⟨by simp⟩
  let q := (ballPrismCollarHomeomorph _).symm (prismAnnulusHomeomorph p)
  change (True ∧ True ∧ q.1 ∈ (stereographic' 1 (-v)).source ∧
    q.2 ∈ (halfOpenStripChart i).source) ↔ _
  rw [true_and, true_and, stereographic'_source, _root_.Set.mem_compl_iff, _root_.Set.mem_singleton_iff,
    mem_halfOpenStripChart_source]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_mem_source_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_mem_source_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_mem_source_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_mem_source_iff

theorem prismAnnulusChart_cover (p : prismAnnulusSource) :
    ∃ v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, ∃ upper : Bool,
      p ∈ (prismAnnulusChart v upper).source := by
  obtain ⟨v, upper, hp⟩ := ballPrismCollarChart_cover 1 (prismAnnulusHomeomorph p)
  exact ⟨v, upper, trivial, hp⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_cover then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_cover"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_cover ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_cover

theorem prismAnnulusChart_transition_mem
    (v w : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (i j : Bool) :
    (prismAnnulusChart v i).symm.trans (prismAnnulusChart w j) ∈
      contDiffGroupoid ∞ ((𝓡 1).prod (𝓡∂ 2)) := by
  let _ := prismAnnulusChartedSpace
  let _ : IsManifold ((𝓡 1).prod (𝓡∂ 2)) ∞ prismAnnulusSource := prismAnnulus_isManifold
  exact (contDiffGroupoid ∞ ((𝓡 1).prod (𝓡∂ 2))).compatible
    (prismAnnulusChart_mem_atlas v i) (prismAnnulusChart_mem_atlas w j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_transition_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_transition_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_transition_mem ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_transition_mem

theorem prismAnnulusChart_attaching_iff
    (v : _root_.Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) (i : Bool) (p : prismAnnulusSource) :
    p.val.val.1 ∈ stdSimplexBoundary 2 ↔
      (prismAnnulusChart v i p).2.val 0 = 0 ∧ (prismAnnulusChart v i p).2.val 1 ≤ 0 := by
  rw [← prismBallHomeomorph_mem_sphere_iff p.val]
  exact ballPrismCollarChart_attaching_iff 1 v i (prismAnnulusHomeomorph p)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_attaching_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_attaching_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_attaching_iff ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.prismAnnulusChart_attaching_iff

end DifferentialGeometry.Topology.PiecewiseLinear
