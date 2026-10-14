import Submission.DifferentialGeometry.Analysis.Heat.Semigroup.Solution.Strong

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace HeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian

private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.HeatEquation.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

omit [NeZero (Module.finrank ℝ E)] in
theorem strongSolutionAt_smooth_representatives_satisfy_heat_equation
    (g : SmoothRiemannianMetric I M)
    {u f : ℝ → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    {t : ℝ}
    (hstrong : IsStrongSolutionAt (I := I) (M := M) g u f t)
    (u_smooth du_smooth f_smooth : SmoothScalar g)
    (hu : smoothToLp (I := I) (M := M) g u_smooth = u t)
    (hdu : HasDerivAt u (smoothToLp (I := I) (M := M) g du_smooth) t)
    (hf : smoothToLp (I := I) (M := M) g f_smooth = f t) :
    du_smooth = u_smooth.laplacian + f_smooth := by
  obtain ⟨u_h, hu_h, hstrong_deriv⟩ := hstrong
  let u_smooth_h : laplacianDomain (I := I) (M := M) g :=
    ⟨smoothToH1Compl (I := I) (M := M) g u_smooth,
      smoothToH1Compl_mem_laplacianDomain (I := I) (M := M) u_smooth⟩
  have hu_h_eq : u_h = u_smooth_h := by
    apply Subtype.ext
    apply H1ComplToLp_injective_on_laplacianDomain (I := I) (M := M) g
    rw [hu_h, ← hu, H1ComplToLp_smoothToH1Compl]
  have hderiv_eq :
      smoothToLp (I := I) (M := M) g du_smooth =
        laplacianOp (I := I) (M := M) g u_h + f t :=
    hdu.unique hstrong_deriv
  apply smoothToLp_injective (I := I) (M := M) g
  rw [map_add, hderiv_eq, hu_h_eq, hf]
  exact congrArg (fun v => v + f t)
    (laplacianOp_smoothToH1Compl_eq_smoothToLp_laplacian
      (I := I) (M := M) u_smooth)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.strongSolutionAt_smooth_representatives_satisfy_heat_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.strongSolutionAt_smooth_representatives_satisfy_heat_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.strongSolutionAt_smooth_representatives_satisfy_heat_equation ``Submission.DifferentialGeometry.Analysis.HeatEquation.strongSolutionAt_smooth_representatives_satisfy_heat_equation

theorem mildSolution_smooth_representatives_satisfy_heat_equation
    (g : SmoothRiemannianMetric I M)
    (u_0 : _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g))
    {f : ℝ → _root_.MeasureTheory.Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)}
    (hf : ContDiff ℝ 1 f) {t : ℝ} (ht : 0 < t)
    (u_smooth du_smooth f_smooth : SmoothScalar g)
    (hu : smoothToLp (I := I) (M := M) g u_smooth =
      mildSolution (I := I) (M := M) g u_0 f t)
    (hdu : smoothToLp (I := I) (M := M) g du_smooth =
      -(heatPower (I := I) (M := M) g 1 t u_0) +
        mildSolution (I := I) (M := M) g (f 0) (deriv f) t)
    (hf_t : smoothToLp (I := I) (M := M) g f_smooth = f t) :
    du_smooth = u_smooth.laplacian + f_smooth := by
  apply strongSolutionAt_smooth_representatives_satisfy_heat_equation
    (I := I) (M := M) g
    (mildSolution_isStrongSolutionAt_of_hasDerivAt_forcing
      (I := I) (M := M) g u_0
      (f' := deriv f)
      (fun s => (hf.differentiable (by norm_num) s).hasDerivAt)
      hf.continuous_deriv_one ht)
    u_smooth du_smooth f_smooth hu
  · rw [hdu]
    exact mildSolution_hasDerivAt_of_contDiff_forcing
      (I := I) (M := M) g u_0 hf ht
  · exact hf_t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.HeatEquation.mildSolution_smooth_representatives_satisfy_heat_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.HeatEquation.mildSolution_smooth_representatives_satisfy_heat_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.HeatEquation.mildSolution_smooth_representatives_satisfy_heat_equation ``Submission.DifferentialGeometry.Analysis.HeatEquation.mildSolution_smooth_representatives_satisfy_heat_equation

end HeatEquation
end Analysis
end DifferentialGeometry

end
