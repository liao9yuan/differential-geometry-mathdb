import Submission.DifferentialGeometry.Analysis.Elliptic.Lichnerowicz
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciOperatorNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

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

theorem scalar_hess_graph
    (g : SmoothRiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f),
      ∫ x, chartHessFrobeniusSq (I := I) g f x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        (∫ x, (ΔG (I := I) g ⟨_, hf⟩ x) ^ 2
          ∂(riemannianVolumeMeasure (I := I) (M := M) g)) +
        C * ∫ x, normGradSqFun (I := I) g f x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  obtain ⟨C, hC, hRic⟩ := exists_ricci_bound (I := I) (M := M) g
  refine ⟨C, hC, ?_⟩
  intro f hf
  let fMap : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ := ⟨f, hf⟩
  let μ : _root_.MeasureTheory.Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  let _ : _root_.MeasureTheory.IsFiniteMeasure μ :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace
      (I := I) (M := M) g
  let Hess : M → ℝ := fun x => chartHessFrobeniusSq (I := I) g f x
  let Ric : M → ℝ := fun x => ricciTensor (I := I) g x
    (gradFun (I := I) g f x) (gradFun (I := I) g f x)
  let Grad : M → ℝ := normGradSqFun (I := I) g f
  let LapSq : M → ℝ := fun x => (ΔG (I := I) g fMap x) ^ 2
  let Cross : M → ℝ := fun x => g.inner x
    (gradFun (I := I) g f x)
    (gradFun (I := I) g (ΔG (I := I) g fMap) x)
  have hΔf : ContMDiff I 𝓘(ℝ, ℝ) ∞ (ΔG (I := I) g fMap) :=
    Δ_g_contMDiff (I := I) g fMap
  let lapMap : C^∞⟮I, M; 𝓘(ℝ, ℝ), ℝ⟯ := ⟨ΔG (I := I) g fMap, hΔf⟩
  have hHess_cont : Continuous Hess := by
    exact chartHessFrobeniusSq_continuous (I := I) g hf
  have hGrad_cont : Continuous Grad := by
    exact normGradSqFun_continuous (I := I) g hf
  have hLapSq_cont : Continuous LapSq := by
    exact hΔf.continuous.pow 2
  have hCross_cont : Continuous Cross := by
    let Gf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := gradG (I := I) g fMap
    let GΔf : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := gradG (I := I) g lapMap
    have h := TangentBundle.continuous_g_inner_of_smooth_sections
      (I := I) (M := M) g Gf GΔf
    change Continuous (fun x => g.inner x (Gf x) (GΔf x))
    exact h
  have hRic_cont : Continuous Ric := by
    have hnormLap : Continuous
        (ΔG (I := I) g ⟨_, (normGradSqFun_contMDiff (I := I) g hf)⟩) :=
      (Δ_g_contMDiff (I := I) g ⟨_, (normGradSqFun_contMDiff (I := I) g hf)⟩).continuous
    have heq : Ric = fun x =>
        (ΔG (I := I) g ⟨_, (normGradSqFun_contMDiff (I := I) g hf)⟩ x -
          2 * Hess x - 2 * Cross x) / 2 := by
      funext x
      have hB := bochner_pointwise_concrete_metric (I := I) g hf x
      dsimp only [Ric, Hess, Cross]
      linarith
    rw [heq]
    exact ((hnormLap.sub (continuous_const.mul hHess_cont)).sub
      (continuous_const.mul hCross_cont)).div_const 2
  have integrable_of_cont : ∀ {q : M → ℝ}, Continuous q → _root_.MeasureTheory.Integrable q μ := by
    intro q hq
    exact hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hHess_int : _root_.MeasureTheory.Integrable Hess μ := integrable_of_cont hHess_cont
  have hRic_int : _root_.MeasureTheory.Integrable Ric μ := integrable_of_cont hRic_cont
  have hGrad_int : _root_.MeasureTheory.Integrable Grad μ := integrable_of_cont hGrad_cont
  have hLapSq_int : _root_.MeasureTheory.Integrable LapSq μ := integrable_of_cont hLapSq_cont
  have hCross_int : _root_.MeasureTheory.Integrable Cross μ := integrable_of_cont hCross_cont
  have hzero :
      ∫ x, ΔG (I := I) g ⟨_, (normGradSqFun_contMDiff (I := I) g hf)⟩ x ∂μ = 0 := by
    exact integral_divergence_eq_zero_of_compact (I := I) g
      (gradG (I := I) g ⟨_, (normGradSqFun_contMDiff (I := I) g hf)⟩)
  have hbochner :
      ∫ x, ΔG (I := I) g ⟨_, (normGradSqFun_contMDiff (I := I) g hf)⟩ x ∂μ =
        ∫ x, (2 * Hess x + 2 * Ric x + 2 * Cross x) ∂μ := by
    refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simpa only [Hess, Ric, Cross] using
      (bochner_pointwise_concrete_metric (I := I) g hf x)
  have hmain :
      0 = 2 * (∫ x, Hess x ∂μ) + 2 * (∫ x, Ric x ∂μ) +
        2 * (∫ x, Cross x ∂μ) := by
    calc
      0 = ∫ x, ΔG (I := I) g ⟨_, (normGradSqFun_contMDiff (I := I) g hf)⟩ x ∂μ := hzero.symm
      _ = ∫ x, (2 * Hess x + 2 * Ric x + 2 * Cross x) ∂μ := hbochner
      _ = 2 * (∫ x, Hess x ∂μ) + 2 * (∫ x, Ric x ∂μ) +
          2 * (∫ x, Cross x ∂μ) := by
        calc
          ∫ x, (2 * Hess x + 2 * Ric x + 2 * Cross x) ∂μ =
              (∫ x, 2 * Hess x + 2 * Ric x ∂μ) +
                ∫ x, 2 * Cross x ∂μ := by
            simpa only [Pi.add_apply] using
              (_root_.MeasureTheory.integral_add
                ((hHess_int.const_mul 2).add (hRic_int.const_mul 2))
                (hCross_int.const_mul 2))
          _ = ((∫ x, 2 * Hess x ∂μ) + ∫ x, 2 * Ric x ∂μ) +
                ∫ x, 2 * Cross x ∂μ := by
            rw [_root_.MeasureTheory.integral_add (hHess_int.const_mul 2) (hRic_int.const_mul 2)]
          _ = 2 * (∫ x, Hess x ∂μ) + 2 * (∫ x, Ric x ∂μ) +
                2 * (∫ x, Cross x ∂μ) := by
            rw [_root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul, _root_.MeasureTheory.integral_const_mul]
  have hcross : ∫ x, Cross x ∂μ = -∫ x, LapSq x ∂μ := by
    calc
      ∫ x, Cross x ∂μ =
          ∫ x, g.inner x
            ((gradG (I := I) g lapMap :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            ((gradG (I := I) g fMap :
              Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x) ∂μ := by
            refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
            change g.inner x (gradFun (I := I) g f x)
                (gradFun (I := I) g (ΔG (I := I) g fMap) x) =
              g.inner x
                ((gradG (I := I) g lapMap :
                  Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
                ((gradG (I := I) g fMap :
                  Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x)
            simp only [grad_g_apply]
            exact g.symm x _ _
      _ = -∫ x, (ΔG (I := I) g fMap x) * (ΔG (I := I) g fMap x) ∂μ :=
        green_first_integral_inner_grad_eq_neg_integral_smul_laplacian
          (I := I) g hΔf hf (HasCompactSupport.of_compactSpace _)
      _ = -∫ x, LapSq x ∂μ := by
        congr 1
        refine _root_.MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [LapSq]
        ring
  have hbalance :
      ∫ x, Hess x ∂μ =
        (∫ x, LapSq x ∂μ) - ∫ x, Ric x ∂μ := by
    rw [hcross] at hmain
    linarith
  have hRic_lower : ∀ x : M, -C * Grad x ≤ Ric x := by
    intro x
    have hx := hRic x (gradFun (I := I) g f x)
    have hx' := (abs_le.mp hx).1
    calc
      -C * Grad x = -(C * normGradSqFun (I := I) g f x) := by
        simp only [Grad]
        ring
      _ ≤ Ric x := by
        simpa only [Ric, normGradSqFun_def] using hx'
  have hRic_int_lower :
      -C * (∫ x, Grad x ∂μ) ≤ ∫ x, Ric x ∂μ := by
    have hmono :
        (∫ x, -C * Grad x ∂μ) ≤ ∫ x, Ric x ∂μ :=
      _root_.MeasureTheory.integral_mono_ae (hGrad_int.const_mul (-C)) hRic_int
        (Filter.Eventually.of_forall hRic_lower)
    rwa [_root_.MeasureTheory.integral_const_mul] at hmono
  rw [show riemannianVolumeMeasure (I := I) (M := M) g = μ from rfl]
  change (∫ x, Hess x ∂μ) ≤
    (∫ x, LapSq x ∂μ) + C * ∫ x, Grad x ∂μ
  rw [hbalance]
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.scalar_hess_graph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.scalar_hess_graph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.scalar_hess_graph ``Submission.DifferentialGeometry.Analysis.Laplacian.scalar_hess_graph

end Laplacian
end Analysis
end DifferentialGeometry

end
