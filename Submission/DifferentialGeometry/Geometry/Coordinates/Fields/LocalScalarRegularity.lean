import Submission.DifferentialGeometry.Geometry.Coordinates.Fields.Scalar

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Set
open scoped _root_.ContDiff _root_.Manifold

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} [IsManifold I n M]

theorem scalarOnE_contDiffOn_of_contMDiffOn
    (x₀ : M) {f : M → ℝ} {U : Set M}
    (hf : ContMDiffOn I 𝓘(ℝ) n f U) :
    ContDiffOn ℝ n (scalarOnE (I := I) x₀ f)
      ((extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' U) := by
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I n (extChartAt I x₀).symm
      ((extChartAt I x₀).target ∩ (extChartAt I x₀).symm ⁻¹' U) :=
    (contMDiffOn_extChartAt_symm (I := I) x₀).mono _root_.Set.inter_subset_left
  exact (hf.comp hsymm (fun _ hy => hy.2)).contDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffOn_of_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffOn_of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffOn_of_contMDiffOn ``Submission.DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffOn_of_contMDiffOn

theorem scalarOnE_contDiffAt_of_contMDiffOn
    [I.Boundaryless] (x₀ : M) {f : M → ℝ} {U : Set M} {y : E}
    (hf : ContMDiffOn I 𝓘(ℝ) n f U) (hU : IsOpen U)
    (hy : y ∈ (extChartAt I x₀).target)
    (hyU : (extChartAt I x₀).symm y ∈ U) :
    ContDiffAt ℝ n (scalarOnE (I := I) x₀ f) y := by
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I n (extChartAt I x₀).symm y :=
    (contMDiffOn_extChartAt_symm (I := I) x₀).contMDiffAt
      (extChartAt_target_mem_nhds' hy)
  exact ((hf.contMDiffAt (hU.mem_nhds hyU)).comp y hsymm).contDiffAt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffAt_of_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffAt_of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffAt_of_contMDiffOn ``Submission.DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffAt_of_contMDiffOn

end DifferentialGeometry.Tensor.Coordinates
