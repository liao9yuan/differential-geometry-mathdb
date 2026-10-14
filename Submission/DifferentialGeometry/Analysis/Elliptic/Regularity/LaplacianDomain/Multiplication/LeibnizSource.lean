import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.GradInner.CLM.Defs
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.SmoothScalar.MulLp
import Submission.DifferentialGeometry.Analysis.Elliptic.Operator.VariationalLaplacian
import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [CompactSpace M]

noncomputable def laplacianOfChartPOU (g : SmoothRiemannianMetric I M) (α : M) :
    C^∞⟮I, M; ℝ⟯ :=
  ⟨ΔG (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯),
    Δ_g_contMDiff (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianOfChartPOU then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianOfChartPOU"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianOfChartPOU ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianOfChartPOU

omit [NeZero (Module.finrank ℝ E)] in
@[simp] lemma laplacianOfChartPOU_apply
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) :
    (laplacianOfChartPOU (I := I) (M := M) g α : M → ℝ) x =
      ΔG (I := I) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.laplacianOfChartPOU_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.laplacianOfChartPOU_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.laplacianOfChartPOU_apply ``Submission.DifferentialGeometry.Analysis.Laplacian.laplacianOfChartPOU_apply

noncomputable def leibnizCompensatedSource (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
      (H1ComplToLp (I := I) (M := M) g u_h -
        laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)
    - (2 : ℝ) • gradInnerCLM (I := I) (M := M) g
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h
    - smoothMulLp (I := I) (M := M) g
        (laplacianOfChartPOU (I := I) (M := M) g α)
        (H1ComplToLp (I := I) (M := M) g u_h)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.leibnizCompensatedSource then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.leibnizCompensatedSource"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.leibnizCompensatedSource ``Submission.DifferentialGeometry.Analysis.Laplacian.leibnizCompensatedSource

abbrev fHLeibniz := leibnizCompensatedSource (I := I) (M := M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.fHLeibniz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.fHLeibniz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.fHLeibniz ``Submission.DifferentialGeometry.Analysis.Laplacian.fHLeibniz

omit [NeZero (Module.finrank ℝ E)] in
lemma fHLeibniz_def (g : SmoothRiemannianMetric I M) (α : M)
    (u_h : H1Compl g) (hu_h : u_h ∈ laplacianDomain (I := I) (M := M) g) :
    leibnizCompensatedSource (I := I) (M := M) g α u_h hu_h =
      smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (H1ComplToLp (I := I) (M := M) g u_h -
            laplacianOp (I := I) (M := M) g ⟨u_h, hu_h⟩)
        - (2 : ℝ) • gradInnerCLM (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) u_h
        - smoothMulLp (I := I) (M := M) g
            (laplacianOfChartPOU (I := I) (M := M) g α)
            (H1ComplToLp (I := I) (M := M) g u_h) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.fHLeibniz_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.fHLeibniz_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.fHLeibniz_def ``Submission.DifferentialGeometry.Analysis.Laplacian.fHLeibniz_def

omit [NeZero (Module.finrank ℝ E)] in
theorem fHLeibniz_smoothToH1Compl (g : SmoothRiemannianMetric I M) (α : M)
    (v : SmoothScalar g) :
    leibnizCompensatedSource (I := I) (M := M) g α
        (smoothToH1Compl (I := I) (M := M) g v)
        (smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v) =
      smoothMulLp (I := I) (M := M) g (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯)
          (smoothToLp (I := I) (M := M) g v.oneSubLapClassical)
        - (2 : ℝ) • gradInnerSmooth (I := I) (M := M) g
            (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) v
        - smoothMulLp (I := I) (M := M) g
            (laplacianOfChartPOU (I := I) (M := M) g α)
            (smoothToLp (I := I) (M := M) g v) := by
  rw [fHLeibniz_def]
  have h_oneSubLap :
      H1ComplToLp (I := I) (M := M) g
          (smoothToH1Compl (I := I) (M := M) g v) -
        laplacianOp (I := I) (M := M) g
          ⟨smoothToH1Compl (I := I) (M := M) g v,
            smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) v⟩ =
      smoothToLp (I := I) (M := M) g v.oneSubLapClassical := by
    rw [H1ComplToLp_smoothToH1Compl, laplacianOp_smoothToH1Compl]
    abel
  rw [h_oneSubLap]
  rw [gradInnerCLM_smoothToH1Compl]
  rw [H1ComplToLp_smoothToH1Compl]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.fHLeibniz_smoothToH1Compl then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.fHLeibniz_smoothToH1Compl"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.fHLeibniz_smoothToH1Compl ``Submission.DifferentialGeometry.Analysis.Laplacian.fHLeibniz_smoothToH1Compl

end Laplacian
end Analysis
end DifferentialGeometry

end
