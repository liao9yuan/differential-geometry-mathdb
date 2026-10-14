import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.ResidualRegularity.BilinearH1ComplFromDomainPow
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Multiplication.H1Completion
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Chart.LocalRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ResidualLpDecomposition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
lemma leibnizCompensatedSourceResidualCLMOfSmoothFactor_eq_fHLeibnizResidualLp
    (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl (I := I) (M := M) g) :
    leibnizCompensatedSourceResidualCLMOfSmoothFactor (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h =
      -((2 : ℝ) • gradInnerCLM (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h) -
        smoothMulLp (I := I) (M := M) g
          (laplacianOfChartPOU (I := I) (M := M) g α)
          (H1ComplToLp (I := I) (M := M) g u_h) := by
  classical
  rw [leibnizCompensatedSourceResidualCLMOfSmoothFactor_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.leibnizCompensatedSourceResidualCLMOfSmoothFactor_eq_fHLeibnizResidualLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.leibnizCompensatedSourceResidualCLMOfSmoothFactor_eq_fHLeibnizResidualLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.leibnizCompensatedSourceResidualCLMOfSmoothFactor_eq_fHLeibnizResidualLp ``Submission.DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.leibnizCompensatedSourceResidualCLMOfSmoothFactor_eq_fHLeibnizResidualLp

omit [NeZero (Module.finrank ℝ E)] in
theorem preimage_smoothMulH1Compl_eq_smoothMulLp_preimage_add_residual
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    laplacianDomain.preimage (I := I) (M := M) g
        ⟨smoothMulH1Compl (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
          smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_dom⟩ =
      smoothMulLp (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩) +
        leibnizCompensatedSourceResidualCLMOfSmoothFactor (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h := by
  classical
  have h_preimage_smoothMulH1Compl :=
    laplacianDomain_preimage_smoothMulH1Compl (I := I) (M := M) g
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_dom
  unfold leibnizCompensatedSourceOfSmoothFactor at h_preimage_smoothMulH1Compl
  have h_diff_eq :
      H1ComplToLp (I := I) (M := M) g u_h -
        laplacianOp (I := I) (M := M) g ⟨u_h, hu_dom⟩ =
      laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩ := by
    rw [laplacianOp_apply]
    abel
  rw [h_diff_eq] at h_preimage_smoothMulH1Compl
  exact h_preimage_smoothMulH1Compl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.preimage_smoothMulH1Compl_eq_smoothMulLp_preimage_add_residual then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.preimage_smoothMulH1Compl_eq_smoothMulLp_preimage_add_residual"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.preimage_smoothMulH1Compl_eq_smoothMulLp_preimage_add_residual ``Submission.DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.preimage_smoothMulH1Compl_eq_smoothMulLp_preimage_add_residual

omit [NeZero (Module.finrank ℝ E)] in
theorem leibnizCompensatedSourceResidualCLMOfSmoothFactor_eq_preimageDiff
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_dom : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    leibnizCompensatedSourceResidualCLMOfSmoothFactor (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h =
      laplacianDomain.preimage (I := I) (M := M) g
          ⟨smoothMulH1Compl (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h,
            smoothMulH1Compl_mem_laplacianDomain (I := I) (M := M) g
              (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) hu_dom⟩ -
        smoothMulLp (I := I) (M := M) g
          (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (laplacianDomain.preimage (I := I) (M := M) g ⟨u_h, hu_dom⟩) := by
  classical
  have h := preimage_smoothMulH1Compl_eq_smoothMulLp_preimage_add_residual
    (I := I) (M := M) g α hu_dom
  rw [h]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.leibnizCompensatedSourceResidualCLMOfSmoothFactor_eq_preimageDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.leibnizCompensatedSourceResidualCLMOfSmoothFactor_eq_preimageDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.leibnizCompensatedSourceResidualCLMOfSmoothFactor_eq_preimageDiff ``Submission.DifferentialGeometry.Analysis.Laplacian.ResidualLpDecomposition.leibnizCompensatedSourceResidualCLMOfSmoothFactor_eq_preimageDiff

end ResidualLpDecomposition
end Laplacian
end Analysis
end DifferentialGeometry

end
