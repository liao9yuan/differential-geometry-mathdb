import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SmoothStructure
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.SeamOrientation
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.LocalDiffeomorphism
import Submission.DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.PuncturedImageBall

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology
open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Topology

noncomputable section
universe u v

namespace OrientationAssembly

abbrev csModel : Type := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.csModel then
    throwError "Refusing to shadow existing declaration OrientationAssembly.csModel"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.csModel ``Submission.OrientationAssembly.csModel
abbrev csSphere : Type := Metric.sphere (0 : csModel) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.csSphere then
    throwError "Refusing to shadow existing declaration OrientationAssembly.csSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.csSphere ``Submission.OrientationAssembly.csSphere

open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Topology.ConnectedSumQuotient

variable {M : Type u} [TopologicalSpace M] [ChartedSpace csModel M] [IsManifold (𝓡 3) ∞ M] [T2Space M]
  {N : Type v} [TopologicalSpace N] [ChartedSpace csModel N] [IsManifold (𝓡 3) ∞ N] [T2Space N]

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem mem_atlas_leftChart (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (a : csSphere ≃ₜ csSphere) (f : OpenPartialHomeomorph M csModel) (hf : f ∈ atlas csModel M) :
    letI := csChartedSpace c d a
    (leftChart c d a hn3 f).symm ∈ atlas csModel (ConnectedSumQuotient c d a) :=
  ⟨Sum.inl ⟨f, hf⟩, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mem_atlas_leftChart then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mem_atlas_leftChart"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mem_atlas_leftChart ``Submission.OrientationAssembly.mem_atlas_leftChart

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem mem_atlas_rightChart (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (a : csSphere ≃ₜ csSphere) (g : OpenPartialHomeomorph N csModel) (hg : g ∈ atlas csModel N) :
    letI := csChartedSpace c d a
    (rightChart c d a hn3 g).symm ∈ atlas csModel (ConnectedSumQuotient c d a) :=
  ⟨Sum.inr (Sum.inl ⟨g, hg⟩), rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mem_atlas_rightChart then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mem_atlas_rightChart"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mem_atlas_rightChart ``Submission.OrientationAssembly.mem_atlas_rightChart

omit [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ N] in
theorem mem_atlas_seamChartX (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (a : csSphere ≃ₜ csSphere) :
    letI := csChartedSpace c d a
    seamChartX c d a ∈ atlas csModel (ConnectedSumQuotient c d a) :=
  ⟨Sum.inr (Sum.inr ()), rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.mem_atlas_seamChartX then
    throwError "Refusing to shadow existing declaration OrientationAssembly.mem_atlas_seamChartX"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.mem_atlas_seamChartX ``Submission.OrientationAssembly.mem_atlas_seamChartX

theorem interiorLeft_isLocalDiffeomorph' (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere) :
    letI := csChartedSpace c d aD.toHomeomorph
    letI := csIsManifold c d aD.toHomeomorph (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (interiorLeft c d aD) := by
  let _ := csChartedSpace c d aD.toHomeomorph
  let _ := csIsManifold c d aD.toHomeomorph (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
  exact interiorLeft_isLocalDiffeomorph c d aD (fun f hf => mem_atlas_leftChart c d aD.toHomeomorph f hf)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.interiorLeft_isLocalDiffeomorph' then
    throwError "Refusing to shadow existing declaration OrientationAssembly.interiorLeft_isLocalDiffeomorph'"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.interiorLeft_isLocalDiffeomorph' ``Submission.OrientationAssembly.interiorLeft_isLocalDiffeomorph'

theorem interiorRight_isLocalDiffeomorph' (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere) :
    letI := csChartedSpace c d aD.toHomeomorph
    letI := csIsManifold c d aD.toHomeomorph (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (interiorRight c d aD) := by
  let _ := csChartedSpace c d aD.toHomeomorph
  let _ := csIsManifold c d aD.toHomeomorph (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
  exact interiorRight_isLocalDiffeomorph c d aD (fun g hg => mem_atlas_rightChart c d aD.toHomeomorph g hg)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.interiorRight_isLocalDiffeomorph' then
    throwError "Refusing to shadow existing declaration OrientationAssembly.interiorRight_isLocalDiffeomorph'"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.interiorRight_isLocalDiffeomorph' ``Submission.OrientationAssembly.interiorRight_isLocalDiffeomorph'

theorem collarMap_isLocalDiffeomorph' (c : BallChart 3 (𝓡 3) M) (d : BallChart 3 (𝓡 3) N)
    (aD : csSphere ≃ₘ⟮𝓡 2, 𝓡 2⟯ csSphere) :
    letI := csChartedSpace c d aD.toHomeomorph
    letI := csIsManifold c d aD.toHomeomorph (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (collarMap c d aD) := by
  let _ := csChartedSpace c d aD.toHomeomorph
  let _ := csIsManifold c d aD.toHomeomorph (contDiffOn_reflectMap aD) (contDiffOn_reflectMapInv aD)
  exact collarMap_isLocalDiffeomorph c d aD (mem_atlas_seamChartX c d aD.toHomeomorph)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `OrientationAssembly.collarMap_isLocalDiffeomorph' then
    throwError "Refusing to shadow existing declaration OrientationAssembly.collarMap_isLocalDiffeomorph'"
  Lean.modifyEnv fun env => Lean.addAlias env `OrientationAssembly.collarMap_isLocalDiffeomorph' ``Submission.OrientationAssembly.collarMap_isLocalDiffeomorph'

end OrientationAssembly

namespace AssemblyReduction
open _root_.Submission.OrientationAssembly
abbrev csModel : Type := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AssemblyReduction.csModel then
    throwError "Refusing to shadow existing declaration AssemblyReduction.csModel"
  Lean.modifyEnv fun env => Lean.addAlias env `AssemblyReduction.csModel ``Submission.AssemblyReduction.csModel
abbrev csSphere : Type := Metric.sphere (0 : csModel) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AssemblyReduction.csSphere then
    throwError "Refusing to shadow existing declaration AssemblyReduction.csSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `AssemblyReduction.csSphere ``Submission.AssemblyReduction.csSphere
open _root_.Submission.DifferentialGeometry.Topology _root_.Submission.DifferentialGeometry.Topology.ConnectedSumQuotient

theorem exists_smooth_connected_sum_of_orientation
    {M : ConnectedClosedOrientedManifold.{u} 3} {N : ConnectedClosedOrientedManifold.{v} 3}
    (c : OrientedBallChart M.toClosedOrientedManifold) (d : OrientedBallChart N.toClosedOrientedManifold)
    (a : BoundaryAttachment)
    (hO :
      letI := csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
      letI := csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
        (contDiffOn_reflectMap a.1) (contDiffOn_reflectMapInv a.1)
      ∃ O : DifferentialGeometry.ManifoldOrientation (𝓡 3)
          (ConnectedSumQuotient c.toBallChart d.toBallChart a.1.toHomeomorph) 3,
        (∀ x : c.toBallChart.interior, Orientation.map (Fin 3)
            ((interiorLeft_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1).mfderivToContinuousLinearEquiv
              (by simp) x).toLinearEquiv (M.orientation.orientation x)
          = O.orientation (ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 x)) ∧
        (∀ x : d.toBallChart.interior, Orientation.map (Fin 3)
            ((interiorRight_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1).mfderivToContinuousLinearEquiv
              (by simp) x).toLinearEquiv (N.orientation.orientation x)
          = O.orientation (ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 x))) :
    Nonempty (SmoothConnectedSum c d a) := by
  let _ := csChartedSpace c.toBallChart d.toBallChart a.1.toHomeomorph
  let _ := csIsManifold c.toBallChart d.toBallChart a.1.toHomeomorph
    (contDiffOn_reflectMap a.1) (contDiffOn_reflectMapInv a.1)
  have : Nonempty (Metric.sphere (0 : csModel) 1) := nonempty_sphere_of_neZero
  obtain ⟨O, hL, hR⟩ := hO
  exact ⟨O, interiorLeft_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1,
    interiorRight_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1,
    collarMap_isLocalDiffeomorph' c.toBallChart d.toBallChart a.1, hL, hR⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `AssemblyReduction.exists_smooth_connected_sum_of_orientation then
    throwError "Refusing to shadow existing declaration AssemblyReduction.exists_smooth_connected_sum_of_orientation"
  Lean.modifyEnv fun env => Lean.addAlias env `AssemblyReduction.exists_smooth_connected_sum_of_orientation ``Submission.AssemblyReduction.exists_smooth_connected_sum_of_orientation

end AssemblyReduction
