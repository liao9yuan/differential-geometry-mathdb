import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPath.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.UniformBochner
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.Bounds.AllTimes
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Curvature.ActionZero

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

structure CurvatureActionParameters where
  rankTwo : ℝ
  rankThree : ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.CurvatureActionParameters then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.CurvatureActionParameters"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.CurvatureActionParameters ``Submission.DifferentialGeometry.PDE.RicciFlow.CurvatureActionParameters

noncomputable def curvatureActionParameters (d : ℕ) (Λ Kb₀ Kb₁ : ℝ) : CurvatureActionParameters where
  rankTwo := uniformPtCurvZeroC d Λ Kb₀ Kb₁
  rankThree := uniformPtCurvThreeC d Λ Kb₀ Kb₁

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.curvatureActionParameters then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.curvatureActionParameters"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.curvatureActionParameters ``Submission.DifferentialGeometry.PDE.RicciFlow.curvatureActionParameters

structure HasUniformCurvatureActionBounds
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (K : CurvatureActionParameters) : Prop where
  bounds : ∀ (g : SmoothRiemannianMetric I M),
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    IsCurvAction0 (I := I) (M := M) g 2 K.rankTwo ∧
      IsCurvAction0 (I := I) (M := M) g 3 K.rankThree

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HasUniformCurvatureActionBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HasUniformCurvatureActionBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HasUniformCurvatureActionBounds ``Submission.DifferentialGeometry.PDE.RicciFlow.HasUniformCurvatureActionBounds

theorem has_uniform_curvature_action_bounds
    (gBase : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀_nonneg : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (LeviCivita (I := I) gBase) x v w u)
          (riemannOp (LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁_nonneg : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁) :
    HasUniformCurvatureActionBounds (I := I) (M := M) gBase Λ
      (curvatureActionParameters (Module.finrank ℝ E) Λ Kb₀ Kb₁) := by
  refine ⟨?_⟩
  intro g hEq hjet
  have hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ Λ * gBase.inner x v v :=
    fun x v => hEq.2 x (Set.mem_univ x) v
  have hjet1 := hjet 1 (by norm_num)
  have hjet2 := hjet 2 (by norm_num)
  have hjet3 := hjet 3 (by norm_num)
  constructor
  · simpa only [curvatureActionParameters] using
      (uniformCurvAction0_of (I := I) (M := M) gBase g hΛ
        hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁ hcomp hjet1 hjet2 hjet3)
  · simpa only [curvatureActionParameters] using
      (uniformCurvAction3_of (I := I) (M := M) gBase g hΛ
        hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁ hcomp hjet1 hjet2 hjet3)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.has_uniform_curvature_action_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.has_uniform_curvature_action_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.has_uniform_curvature_action_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.has_uniform_curvature_action_bounds

theorem exists_uniform_curvature_action_parameters
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ K : CurvatureActionParameters, HasUniformCurvatureActionBounds (I := I) (M := M) gBase Λ K := by
  obtain ⟨Kb₀, hKb₀_nonneg, hKb₀⟩ :=
    exists_uniform_riemannOp_LeviCivita_gNorm_bound (I := I) (M := M) gBase
  obtain ⟨Kb₁, hKb₁_nonneg, hKb₁⟩ :=
    exists_curvJet_sup (I := I) (M := M) gBase 1
  have hKb₁' : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁ := by
    intro x
    simpa using hKb₁ x
  exact ⟨curvatureActionParameters (Module.finrank ℝ E) Λ Kb₀ Kb₁,
    has_uniform_curvature_action_bounds (I := I) (M := M) gBase hΛ
      hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁'⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_uniform_curvature_action_parameters then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_uniform_curvature_action_parameters"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_uniform_curvature_action_parameters ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_uniform_curvature_action_parameters

noncomputable def convexSecondOrderConstant (K : CurvatureActionParameters) : ℝ :=
  h2CovsumC K.rankTwo

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.convexSecondOrderConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.convexSecondOrderConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.convexSecondOrderConstant ``Submission.DifferentialGeometry.PDE.RicciFlow.convexSecondOrderConstant

noncomputable def convexThirdOrderConstant (K : CurvatureActionParameters) : ℝ :=
  h3CovsumC K.rankTwo K.rankThree

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.convexThirdOrderConstant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.convexThirdOrderConstant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.convexThirdOrderConstant ``Submission.DifferentialGeometry.PDE.RicciFlow.convexThirdOrderConstant

structure ConvexJetConstants where
  secondOrder : ℝ
  thirdOrder : ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ConvexJetConstants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ConvexJetConstants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ConvexJetConstants ``Submission.DifferentialGeometry.PDE.RicciFlow.ConvexJetConstants

noncomputable def convexJetConstants (K : CurvatureActionParameters) : ConvexJetConstants where
  secondOrder := convexSecondOrderConstant K
  thirdOrder := convexThirdOrderConstant K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.convexJetConstants then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.convexJetConstants"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.convexJetConstants ``Submission.DifferentialGeometry.PDE.RicciFlow.convexJetConstants

structure HasUniformConvexPerturbationJetBounds
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (C : ConvexJetConstants) : Prop where
  secondOrder_nonneg : 0 ≤ C.secondOrder
  thirdOrder_nonneg : 0 ≤ C.thirdOrder
  bounds : ∀ (g : SmoothRiemannianMetric I M),
    MetricUniformEquivalentOn (I := I) Set.univ gBase g Λ →
    (∀ a : ℕ, a ≤ 3 →
      MetricCovDerivOrderBoundOn (I := I) Set.univ a g gBase Λ) →
    (∀ (T T' : SmoothCcTensor g 0 2) (R : ℝ), 0 ≤ R →
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T‖ ≤ R →
      ‖ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) T'‖ ≤ R →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        (∑ j ∈ Finset.range 3,
          ‖iteratedCovGrad (I := I) g 0 2 j
            (convexPerturbation (I := I) g T T' s)‖ ^ 2) ≤
          (C.secondOrder * R) ^ 2) ∧
    (∀ (T T' : SmoothCcTensor g 0 2) (R : ℝ), 0 ≤ R →
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T‖ ≤ R →
      ‖ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) T'‖ ≤ R →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        (∑ j ∈ Finset.range 4,
          ‖iteratedCovGrad (I := I) g 0 2 j
            (convexPerturbation (I := I) g T T' s)‖ ^ 2) ≤
          (C.thirdOrder * R) ^ 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.HasUniformConvexPerturbationJetBounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.HasUniformConvexPerturbationJetBounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.HasUniformConvexPerturbationJetBounds ``Submission.DifferentialGeometry.PDE.RicciFlow.HasUniformConvexPerturbationJetBounds

private theorem convex_hs_norm_le
    (g : SmoothRiemannianMetric I M) (q : ℝ)
    (T T' : SmoothCcTensor g 0 2) {R s : ℝ} (_hR : 0 ≤ R)
    (hT : ‖ccTensorToHs (I := I) (M := M) g 2 q T‖ ≤ R)
    (hT' : ‖ccTensorToHs (I := I) (M := M) g 2 q T'‖ ≤ R)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖ccTensorToHs (I := I) (M := M) g 2 q
      (convexPerturbation (I := I) g T T' s)‖ ≤ R := by
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have h1ms : (0 : ℝ) ≤ 1 - s := by linarith [hs.2]
  rw [show convexPerturbation (I := I) g T T' s =
      (1 - s) • T' + s • T from rfl,
    ccTensorToHs_add, ccTensorToHs_smul, ccTensorToHs_smul]
  calc
    ‖(1 - s) • ccTensorToHs (I := I) (M := M) g 2 q T' +
        s • ccTensorToHs (I := I) (M := M) g 2 q T‖
        ≤ ‖(1 - s) • ccTensorToHs (I := I) (M := M) g 2 q T'‖ +
          ‖s • ccTensorToHs (I := I) (M := M) g 2 q T‖ := norm_add_le _ _
    _ = (1 - s) * ‖ccTensorToHs (I := I) (M := M) g 2 q T'‖ +
          s * ‖ccTensorToHs (I := I) (M := M) g 2 q T‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg h1ms, abs_of_nonneg hs0]
    _ ≤ (1 - s) * R + s * R :=
      add_le_add (mul_le_mul_of_nonneg_left hT' h1ms)
        (mul_le_mul_of_nonneg_left hT hs0)
    _ = R := by ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.convex_hs_norm_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.convex_hs_norm_le target :: scope.openDecls } }

theorem convex_h23_of_act
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (K : CurvatureActionParameters)
    (hK : HasUniformCurvatureActionBounds (I := I) (M := M) gBase Λ K) :
    HasUniformConvexPerturbationJetBounds (I := I) (M := M) gBase Λ (convexJetConstants K) := by
  refine ⟨h2CovsumC_nonneg K.rankTwo,
    h3CovsumC_nonneg K.rankTwo K.rankThree, ?_⟩
  intro g hEq hjet
  obtain ⟨hact₂, hact₃⟩ := hK.bounds g hEq hjet
  constructor
  · intro T T' R hR hT hT' s hs
    have hpath := convex_hs_norm_le (I := I) (M := M) g 2 T T' hR hT hT' hs
    have hsum := covsum_hs_two (I := I) (M := M) g 2 hact₂
      (convexPerturbation (I := I) g T T' s)
    have hsum' : (∑ j ∈ Finset.range 3,
        ‖iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T T' s)‖) ≤
        h2CovsumC K.rankTwo * R := by
      exact hsum.trans
        (mul_le_mul_of_nonneg_left hpath (h2CovsumC_nonneg K.rankTwo))
    exact (Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => norm_nonneg
        (iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T T' s)))).trans
      (pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j
            (convexPerturbation (I := I) g T T' s))) hsum' 2)
  · intro T T' R hR hT hT' s hs
    have hpath := convex_hs_norm_le (I := I) (M := M) g 3 T T' hR hT hT' hs
    have hsum := covsum_hs_three (I := I) (M := M) g 2 hact₂ hact₃
      (convexPerturbation (I := I) g T T' s)
    have hsum' : (∑ j ∈ Finset.range 4,
        ‖iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T T' s)‖) ≤
        h3CovsumC K.rankTwo K.rankThree * R := by
      exact hsum.trans
        (mul_le_mul_of_nonneg_left hpath
          (h3CovsumC_nonneg K.rankTwo K.rankThree))
    exact (Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => norm_nonneg
        (iteratedCovGrad (I := I) g 0 2 j
          (convexPerturbation (I := I) g T T' s)))).trans
      (pow_le_pow_left₀
        (Finset.sum_nonneg fun j _ => norm_nonneg
          (iteratedCovGrad (I := I) g 0 2 j
            (convexPerturbation (I := I) g T T' s))) hsum' 2)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.convex_h23_of_act then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.convex_h23_of_act"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.convex_h23_of_act ``Submission.DifferentialGeometry.PDE.RicciFlow.convex_h23_of_act

theorem convex_jets_of_act
    (gBase : SmoothRiemannianMetric I M) (Λ : ℝ) (K : CurvatureActionParameters)
    (hK : HasUniformCurvatureActionBounds (I := I) (M := M) gBase Λ K) :
    ∃ C : ConvexJetConstants, HasUniformConvexPerturbationJetBounds (I := I) (M := M) gBase Λ C :=
  ⟨convexJetConstants K, convex_h23_of_act (I := I) (M := M) gBase Λ K hK⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.convex_jets_of_act then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.convex_jets_of_act"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.convex_jets_of_act ``Submission.DifferentialGeometry.PDE.RicciFlow.convex_jets_of_act

theorem uniform_convex_perturbation_sobolev_two_three_bounds
    (gBase : SmoothRiemannianMetric I M) {Λ Kb₀ Kb₁ : ℝ}
    (hΛ : 1 ≤ Λ)
    (hKb₀_nonneg : 0 ≤ Kb₀)
    (hKb₀ : ∀ (x : M) (v w u : TangentSpace I x),
      gBase.inner x (riemannOp (LeviCivita (I := I) gBase) x v w u)
          (riemannOp (LeviCivita (I := I) gBase) x v w u) ≤
        Kb₀ * gBase.inner x v v * gBase.inner x w w * gBase.inner x u u)
    (hKb₁_nonneg : 0 ≤ Kb₁)
    (hKb₁ : ∀ x : M,
      Real.sqrt (normSq0S (I := I) gBase x 5
        (iterCov (I := I) gBase 4
          (metricRm04 (I := I) (M := M) gBase) 1 x)) ≤ Kb₁) :
    HasUniformConvexPerturbationJetBounds (I := I) (M := M) gBase Λ
      (convexJetConstants
        (curvatureActionParameters (Module.finrank ℝ E) Λ Kb₀ Kb₁)) := by
  exact convex_h23_of_act (I := I) (M := M) gBase Λ
    (curvatureActionParameters (Module.finrank ℝ E) Λ Kb₀ Kb₁)
    (has_uniform_curvature_action_bounds (I := I) (M := M) gBase hΛ
      hKb₀_nonneg hKb₀ hKb₁_nonneg hKb₁)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.uniform_convex_perturbation_sobolev_two_three_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.uniform_convex_perturbation_sobolev_two_three_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.uniform_convex_perturbation_sobolev_two_three_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.uniform_convex_perturbation_sobolev_two_three_bounds

theorem exists_convex_jets
    (gBase : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    ∃ C : ConvexJetConstants, HasUniformConvexPerturbationJetBounds (I := I) (M := M) gBase Λ C := by
  obtain ⟨K, hK⟩ := exists_uniform_curvature_action_parameters (I := I) (M := M) gBase hΛ
  exact convex_jets_of_act (I := I) (M := M) gBase Λ K hK

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_convex_jets then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_convex_jets"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_convex_jets ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_convex_jets

end RicciFlow
end PDE
end DifferentialGeometry

end
