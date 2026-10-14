import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ImageLine
import Submission.DifferentialGeometry.Geometry.Connection.GlobalParallelLine

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Submission.DifferentialGeometry.Geometry.Connection.Submission.ContMDiffVectorSubbundle.covariantDerivative_eq_zero_of_unit_of_rank_eq_one then
    throwError "Refusing to shadow existing declaration Submission.DifferentialGeometry.Geometry.Connection.Submission.ContMDiffVectorSubbundle.covariantDerivative_eq_zero_of_unit_of_rank_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Submission.DifferentialGeometry.Geometry.Connection.Submission.ContMDiffVectorSubbundle.covariantDerivative_eq_zero_of_unit_of_rank_eq_one ``Submission.DifferentialGeometry.Geometry.Connection.ContMDiffVectorSubbundle.covariantDerivative_eq_zero_of_unit_of_rank_eq_one
run_cmd do
  let env ← Lean.getEnv
  if env.contains `Submission.DifferentialGeometry.Geometry.Connection.Submission.ContMDiffVectorSubbundle.exists_global_parallel_unit_section_of_rank_eq_one then
    throwError "Refusing to shadow existing declaration Submission.DifferentialGeometry.Geometry.Connection.Submission.ContMDiffVectorSubbundle.exists_global_parallel_unit_section_of_rank_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `Submission.DifferentialGeometry.Geometry.Connection.Submission.ContMDiffVectorSubbundle.exists_global_parallel_unit_section_of_rank_eq_one ``Submission.DifferentialGeometry.Geometry.Connection.ContMDiffVectorSubbundle.exists_global_parallel_unit_section_of_rank_eq_one

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_common_global_parallel_unit_section_of_curvatureOperatorImageAnnihilator_eq
    [SimplyConnectedSpace M]
    {A : Type*} (g : A → SmoothRiemannianMetric I M) (a₀ : A)
    (hdim : Module.finrank ℝ E = 3)
    (hrank : ∀ a y, Module.finrank ℝ (curvatureOperatorImageAt (g a) y
      ⟨metricRm04At (g a) y, metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a) y⟩) = 1)
    (hkernel : ∀ a, IsParallelContinuousAlternatingSubmoduleFamily (g a)
      (fun y => curvatureOperatorKernelAt (g a) y
        ⟨metricRm04At (g a) y, metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a) y⟩))
    (hline : ∀ a y, curvatureOperatorImageAnnihilatorAt (g a) y
      ⟨metricRm04At (g a) y, metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a) y⟩ =
        curvatureOperatorImageAnnihilatorAt (g a₀) y
          ⟨metricRm04At (g a₀) y, metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a₀) y⟩)
    (hdual : ∀ a y, ∀ v ∈ curvatureOperatorImageAnnihilatorAt (g a₀) y
      ⟨metricRm04At (g a₀) y, metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a₀) y⟩,
      ∀ w, (g a).inner y v w = (g a₀).inner y v w) :
    ∃ s : Cₛ^∞⟮I; E, TangentSpace I⟯,
      (∀ a y, s y ∈ curvatureOperatorImageAnnihilatorAt (g a) y
        ⟨metricRm04At (g a) y, metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a) y⟩) ∧
      (∀ a y, (g a).inner y (s y) (s y) = 1) ∧
      (∀ a y, ∀ v : TangentSpace I y, (LeviCivita (g a)) s y v = 0) ∧
      ∀ a y, ∀ v : TangentSpace I y,
        (g a).inner y (s y) v = (g a₀).inner y (s y) v := by
  have hex a := exists_smooth_parallel_curvatureOperatorImageLine hdim (g a) (metricRm04 (g a))
    (fun y => metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a) y)
    (hrank a) (hkernel a)
  obtain ⟨L, hLrank, hLfiber, hLparallel⟩ := hex a₀
  obtain ⟨s, hs_mem, hs_unit, -⟩ :=
    L.exists_global_parallel_unit_section_of_rank_eq_one (g a₀) hLrank hLparallel
  have hmem a y : s y ∈ curvatureOperatorImageAnnihilatorAt (g a) y
      ⟨metricRm04At (g a) y, metricRm04At_mem_algebraicCurvatureTensorSubmodule (g a) y⟩ := by
    rw [hline a y]
    exact hLfiber y ▸ hs_mem y
  have hinner a y v : (g a).inner y (s y) v = (g a₀).inner y (s y) v :=
    hdual a y (s y) (hmem a₀ y) v
  have hunit a y : (g a).inner y (s y) (s y) = 1 :=
    (hinner a y (s y)).trans (hs_unit y)
  refine ⟨s, hmem, hunit, ?_, hinner⟩
  intro a y v
  obtain ⟨La, hLarank, hLafiber, hLaparallel⟩ := hex a
  exact La.covariantDerivative_eq_zero_of_unit_of_rank_eq_one (g a) hLarank hLaparallel
    _root_.Set.univ isOpen_univ s (fun z _ => (hLafiber z).symm ▸ hmem a z)
    (fun z _ => hunit a z) y (_root_.Set.mem_univ y) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Curvature.exists_common_global_parallel_unit_section_of_curvatureOperatorImageAnnihilator_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Curvature.exists_common_global_parallel_unit_section_of_curvatureOperatorImageAnnihilator_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Curvature.exists_common_global_parallel_unit_section_of_curvatureOperatorImageAnnihilator_eq ``Submission.DifferentialGeometry.Geometry.Curvature.exists_common_global_parallel_unit_section_of_curvatureOperatorImageAnnihilator_eq

end DifferentialGeometry.Geometry.Curvature
