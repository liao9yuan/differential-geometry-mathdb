import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.VossWeylFormula
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification
import Submission.DifferentialGeometry.Bundle.SmoothScalarGerm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Tensor.Coordinates
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Geometry.Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

omit [I.Boundaryless] in
theorem chartVossWeylLaplacian_congr_of_eventuallyEq
    (g : SmoothRiemannianMetric I M) (a : M) {f h : M → ℝ} {x : M}
    (hx : x ∈ (extChartAt I a).source) (heq : f =ᶠ[𝓝 x] h) :
    chartVossWeylLaplacian g a f x = chartVossWeylLaplacian g a h x := by
  have hsymm : _root_.Filter.Tendsto (extChartAt I a).symm (𝓝 (extChartAt I a x)) (𝓝 x) := by
    simpa only [(extChartAt I a).left_inv hx] using
      (continuousAt_extChartAt_symm' (I := I) hx).tendsto
  have hs : scalarOnE (I := I) a f =ᶠ[𝓝 (extChartAt I a x)]
      scalarOnE (I := I) a h := heq.comp_tendsto hsymm
  have hi (i : Fin (Module.finrank ℝ E)) :
      chartVossWeylIntegrand g a f i =ᶠ[𝓝 (extChartAt I a x)]
        chartVossWeylIntegrand g a h i := by
    filter_upwards [hs.fderiv (𝕜 := ℝ)] with y hy
    simp only [chartVossWeylIntegrand, gradChartCoeffOnE, partialDeriv, hy]
  unfold chartVossWeylLaplacian
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  unfold partialDeriv
  rw [(hi i).fderiv_eq]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.chartVossWeylLaplacian_congr_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.chartVossWeylLaplacian_congr_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.chartVossWeylLaplacian_congr_of_eventuallyEq ``Submission.DifferentialGeometry.Geometry.Operator.chartVossWeylLaplacian_congr_of_eventuallyEq

theorem laplacian_eq_chartVossWeyl_of_contMDiffOn
    [T2Space M]
    (g : SmoothRiemannianMetric I M) (a : M) {f : M → ℝ} {U : Set M} {x : M}
    (hU : IsOpen U) (hxU : x ∈ U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hx : x ∈ (chartAt H a).source) :
    laplacian (Connection.LeviCivita g) g f x = chartVossWeylLaplacian g a f x := by
  obtain ⟨F, hF, hFf⟩ := exists_smooth_germ hU hxU hf
  calc
    laplacian (Connection.LeviCivita g) g f x =
        laplacian (Connection.LeviCivita g) g F x :=
      laplacian_congr_of_eventuallyEq (Connection.LeviCivita g) g
        (hf.contMDiffAt (hU.mem_nhds hxU)) hF.contMDiffAt hFf.symm
    _ = ΔG g ⟨F, hF⟩ x := laplacian_levi_eq g hF x
    _ = chartVossWeylLaplacian g a F x :=
      voss_weyl_laplacian_formula_pointwise g a hF hx
    _ = chartVossWeylLaplacian g a f x :=
      chartVossWeylLaplacian_congr_of_eventuallyEq g a
        (by rwa [extChartAt_source (I := I) a]) hFf

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Operator.laplacian_eq_chartVossWeyl_of_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Operator.laplacian_eq_chartVossWeyl_of_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Operator.laplacian_eq_chartVossWeyl_of_contMDiffOn ``Submission.DifferentialGeometry.Geometry.Operator.laplacian_eq_chartVossWeyl_of_contMDiffOn

end DifferentialGeometry.Geometry.Operator
