import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Bochner.Polarised

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
  RealInnerProductSpace ENNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace BochnerPolarisedLpSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.GradInnerLpIdentity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainSmoothMul
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.HessianPairingChart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarised

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma contMDiff_phi_add_v
    (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y + (v : M → ℝ) y) :=
  φ.contMDiff.add v.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.contMDiff_phi_add_v then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.contMDiff_phi_add_v"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.contMDiff_phi_add_v ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.contMDiff_phi_add_v

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [IsManifold I ∞ M] [CompactSpace M]
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
lemma contMDiff_phi_sub_v
    (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun y : M => (φ : M → ℝ) y - (v : M → ℝ) y) :=
  φ.contMDiff.sub v.contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.contMDiff_phi_sub_v then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.contMDiff_phi_sub_v"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.contMDiff_phi_sub_v ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.contMDiff_phi_sub_v

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma contMDiff_g_inner_grad_phi_grad_v
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) :
    ContMDiff I 𝓘(ℝ) ∞ (fun b : M => g.inner b
      (gradFun (I := I) g (φ : M → ℝ) b)
      (gradFun (I := I) g (v : M → ℝ) b)) := by
  have h := contMDiff_g_inner_of_smooth_sections (I := I) (M := M) g
    (gradG (I := I) g φ) (gradG (I := I) g v)
  refine h.congr ?_
  intro b
  simp only [grad_g_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.contMDiff_g_inner_grad_phi_grad_v then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.contMDiff_g_inner_grad_phi_grad_v"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.contMDiff_g_inner_grad_phi_grad_v ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.contMDiff_g_inner_grad_phi_grad_v

omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem bochner_polarised_pointwise
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (x : M) :
    ΔG (I := I) g ⟨_, (contMDiff_g_inner_grad_phi_grad_v (I := I) (M := M) g φ v)⟩ x =
      g.inner x
          (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (ΔG (I := I) g v) x) +
        g.inner x
          (gradFun (I := I) g (v : M → ℝ) x)
          (gradFun (I := I) g (ΔG (I := I) g φ) x) +
        2 * hessPairingChart (I := I) g φ v x +
        2 * ricciTensor (I := I) g x
              (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (v : M → ℝ) x) :=
  bochner_polarised_pointwise_of_smoothness (I := I) (M := M) g φ v
    (contMDiff_phi_add_v (I := I) (M := M) φ v)
    (contMDiff_phi_sub_v (I := I) (M := M) φ v)
    (contMDiff_g_inner_grad_phi_grad_v (I := I) (M := M) g φ v) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.bochner_polarised_pointwise then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.bochner_polarised_pointwise"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.bochner_polarised_pointwise ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.bochner_polarised_pointwise

omit [CompactSpace M] in
omit [SigmaCompactSpace M] in
theorem bochner_polarised_pointwise_oneSubLap
    (g : SmoothRiemannianMetric I M) (φ v : C^∞⟮I, M; ℝ⟯) (x : M) :
    g.inner x
        (gradFun (I := I) g (φ : M → ℝ) x)
        (gradFun (I := I) g (v : M → ℝ) x) -
      ΔG (I := I) g ⟨_, (contMDiff_g_inner_grad_phi_grad_v (I := I) (M := M) g φ v)⟩ x =
      g.inner x
          (gradFun (I := I) g (φ : M → ℝ) x)
          (gradFun (I := I) g (v : M → ℝ) x)
        - g.inner x
            (gradFun (I := I) g (v : M → ℝ) x)
            (gradFun (I := I) g (ΔG (I := I) g φ) x)
        - g.inner x
            (gradFun (I := I) g (φ : M → ℝ) x)
            (gradFun (I := I) g (ΔG (I := I) g v) x)
        - 2 * hessPairingChart (I := I) g φ v x
        - 2 * ricciTensor (I := I) g x
              (gradFun (I := I) g (φ : M → ℝ) x)
              (gradFun (I := I) g (v : M → ℝ) x) :=
  bochner_polarised_pointwise_oneSubLap_of_smoothness (I := I) (M := M) g φ v
    (contMDiff_phi_add_v (I := I) (M := M) φ v)
    (contMDiff_phi_sub_v (I := I) (M := M) φ v)
    (contMDiff_g_inner_grad_phi_grad_v (I := I) (M := M) g φ v) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.bochner_polarised_pointwise_oneSubLap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.bochner_polarised_pointwise_oneSubLap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.bochner_polarised_pointwise_oneSubLap ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.bochner_polarised_pointwise_oneSubLap

omit [CompactSpace M] [T2Space M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gradInnerSmoothBundle_toFun
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (b : M) :
    (gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun b =
      g.inner b
        (gradFun (I := I) g (φ : M → ℝ) b)
        (gradFun (I := I) g v.toFun b) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.gradInnerSmoothBundle_toFun then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.gradInnerSmoothBundle_toFun"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.gradInnerSmoothBundle_toFun ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.gradInnerSmoothBundle_toFun

omit [T2Space M] [CompactSpace M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
lemma Δ_g_gradInnerSmoothBundle_eq_contMDiff_g_inner
    (g : SmoothRiemannianMetric I M) (φ : C^∞⟮I, M; ℝ⟯) (v : SmoothScalar g) (x : M) :
    ΔG (I := I) g ⟨(gradInnerSmoothBundle (I := I) (M := M) g φ v).toFun,
      (gradInnerSmoothBundle (I := I) (M := M) g φ v).smooth⟩ x =
      ΔG (I := I) g ⟨_, (contMDiff_g_inner_grad_phi_grad_v (I := I) (M := M) g φ ⟨v.toFun,
        v.smooth⟩)⟩ x := by
  apply Δ_g_congr_func

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.Δ_g_gradInnerSmoothBundle_eq_contMDiff_g_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.Δ_g_gradInnerSmoothBundle_eq_contMDiff_g_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.Δ_g_gradInnerSmoothBundle_eq_contMDiff_g_inner ``Submission.DifferentialGeometry.Analysis.Laplacian.BochnerPolarisedLpSmooth.Δ_g_gradInnerSmoothBundle_eq_contMDiff_g_inner

end BochnerPolarisedLpSmooth
end Laplacian
end Analysis
end DifferentialGeometry

end
