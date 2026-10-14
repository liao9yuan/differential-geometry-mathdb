import Submission.DifferentialGeometry.Analysis.Elliptic.Lichnerowicz
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Hessian.Lp.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianPairingChart

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem


private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

noncomputable def hessPairingChart
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (b : M) : ℝ :=
  (chartHessFrobeniusSq (I := I) g
        (fun x : M => φ x + v x) b -
      chartHessFrobeniusSq (I := I) g
        (fun x : M => φ x - v x) b) / 4

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
@[simp] lemma hessPairingChart_def
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (b : M) :
    hessPairingChart (I := I) g φ v b =
      (chartHessFrobeniusSq (I := I) g
            (fun x : M => φ x + v x) b -
          chartHessFrobeniusSq (I := I) g
            (fun x : M => φ x - v x) b) / 4 := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart_def ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart_def

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma smoothAddOfTwoSmooth
    (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => φ x + v x) :=
  φ.contMDiff.add v.contMDiff

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.smoothAddOfTwoSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.smoothAddOfTwoSmooth target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private lemma smoothSubOfTwoSmooth
    (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x : M => φ x - v x) :=
  φ.contMDiff.sub v.contMDiff

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.smoothSubOfTwoSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.smoothSubOfTwoSmooth target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
omit [CompactSpace M] in
theorem hessPairingChart_continuous
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) :
    Continuous (hessPairingChart (I := I) g φ v) := by
  classical
  unfold hessPairingChart
  have h1 := chartHessFrobeniusSq_continuous (I := I) g
    (smoothAddOfTwoSmooth (I := I) φ v)
  have h2 := chartHessFrobeniusSq_continuous (I := I) g
    (smoothSubOfTwoSmooth (I := I) φ v)
  exact (h1.sub h2).div_const 4

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart_continuous then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart_continuous"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart_continuous ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart_continuous

theorem hessPairingChart_memLp_two
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) :
    MemLp (hessPairingChart (I := I) g φ v) 2
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have : _root_.MeasureTheory.IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := M) g
  exact (hessPairingChart_continuous (I := I) g φ v).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart_memLp_two then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart_memLp_two"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart_memLp_two ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingChart_memLp_two

noncomputable def smoothScalarToContMDiffMap
    {g : SmoothRiemannianMetric I M} (v : SmoothScalar g) : C^∞⟮I, M; ℝ⟯ :=
  ⟨v.toFun, v.smooth⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.smoothScalarToContMDiffMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.smoothScalarToContMDiffMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.smoothScalarToContMDiffMap ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.smoothScalarToContMDiffMap

noncomputable def hessPairingSmoothLp
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (hessPairingChart_memLp_two (I := I) g φ
      (smoothScalarToContMDiffMap (I := I) (g := g) v)).toLp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingSmoothLp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingSmoothLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingSmoothLp ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingSmoothLp

@[simp] lemma hessPairingSmoothLp_def
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    hessPairingSmoothLp (I := I) (M := M) g φ v =
      (hessPairingChart_memLp_two (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v)).toLp _ := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingSmoothLp_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingSmoothLp_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingSmoothLp_def ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingSmoothLp_def

lemma hessPairingSmoothLp_coeFn
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) :
    (hessPairingSmoothLp (I := I) (M := M) g φ v :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =ᵐ[
        riemannianVolumeMeasure (I := I) (M := M) g]
      (hessPairingChart (I := I) g φ
        (smoothScalarToContMDiffMap (I := I) (g := g) v)) :=
  MemLp.coeFn_toLp _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingSmoothLp_coeFn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingSmoothLp_coeFn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingSmoothLp_coeFn ``Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart.hessPairingSmoothLp_coeFn

end HessianPairingChart
end Laplacian
end Analysis
end DifferentialGeometry

end
