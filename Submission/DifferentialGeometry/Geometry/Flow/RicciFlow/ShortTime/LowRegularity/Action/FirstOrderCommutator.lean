import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.LowRegularity.Action.LowerScaleSobolevExtensions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.BigOperators _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] in
omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem jetNN
    (g : SmoothRiemannianMetric I M) {r s m : ℕ}
    (S : SmoothCcTensor g r s) :
    0 ≤ covariantJetNormSq (I := I) (M := M) g m S :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.jetNN
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.jetNN target :: scope.openDecls } }

private theorem firstOrderAction_jet_bound
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g) :
    ∃ Q : ℝ, 0 ≤ Q ∧
      (∀ W : SmoothCcTensor g 0 2,
        covariantJetNormSq (I := I) (M := M) g 2
            (A.firstOrderAction (I := I) (M := M) W) ≤
          Q * covariantJetNormSq (I := I) (M := M) g 3 W) ∧
      (∀ W : SmoothCcTensor g 0 2,
        covariantJetNormSq (I := I) (M := M) g 1
            (A.firstOrderAction (I := I) (M := M) W) ≤
          Q * covariantJetNormSq (I := I) (M := M) g 2 W) := by
  obtain ⟨Ch, hCh, hhigh⟩ :=
    exists_lowerScaleFirstOrderAction_thirdToSecondOrder_bound (I := I) (M := M) hDim g
  obtain ⟨Cl, hCl, hlow⟩ :=
    exists_lowerScaleFirstOrderAction_secondToFirstOrder_bound (I := I) (M := M) hDim g
  let J : ℝ :=
    covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
      covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient
  let B : ℝ := Real.sqrt J
  let C : ℝ := Ch + Cl
  let Q : ℝ := (C * B) ^ 2
  have hJ : 0 ≤ J := by
    exact add_nonneg
      (jetNN (I := I) (M := M) g A.zeroOrderCoefficient)
      (jetNN (I := I) (M := M) g A.firstOrderCoefficient)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  have hBsq : B ^ 2 = J := by
    simpa only [B] using Real.sq_sqrt hJ
  have hC : 0 ≤ C := add_nonneg hCh hCl
  have hQ : 0 ≤ Q := sq_nonneg _
  have hcoeff :
      covariantJetNormSq (I := I) (M := M) g 2 A.zeroOrderCoefficient +
          covariantJetNormSq (I := I) (M := M) g 2 A.firstOrderCoefficient ≤ B ^ 2 := by
    rw [hBsq]
  have hHi : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderAction (I := I) (M := M) W) ≤
        Q * covariantJetNormSq (I := I) (M := M) g 3 W := by
    intro W
    let D : ℝ :=
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 3 W)
    have hW : 0 ≤ covariantJetNormSq (I := I) (M := M) g 3 W :=
      jetNN (I := I) (M := M) g W
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq :
        D ^ 2 = covariantJetNormSq (I := I) (M := M) g 3 W := by
      simpa only [D] using Real.sq_sqrt hW
    calc
      covariantJetNormSq (I := I) (M := M) g 2
          (A.firstOrderAction (I := I) (M := M) W) ≤
        (Ch * B * D) ^ 2 :=
          hhigh A W B D hB hD hcoeff (by rw [hDsq])
      _ ≤ (C * B * D) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCh hB) hD)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_right hCl) hB) hD) 2
      _ = Q * covariantJetNormSq (I := I) (M := M) g 3 W := by
        rw [show (C * B * D) ^ 2 = (C * B) ^ 2 * D ^ 2 by ring,
          hDsq]
  have hLo : ∀ W : SmoothCcTensor g 0 2,
      covariantJetNormSq (I := I) (M := M) g 1
          (A.firstOrderAction (I := I) (M := M) W) ≤
        Q * covariantJetNormSq (I := I) (M := M) g 2 W := by
    intro W
    let D : ℝ :=
      Real.sqrt (covariantJetNormSq (I := I) (M := M) g 2 W)
    have hW : 0 ≤ covariantJetNormSq (I := I) (M := M) g 2 W :=
      jetNN (I := I) (M := M) g W
    have hD : 0 ≤ D := Real.sqrt_nonneg _
    have hDsq :
        D ^ 2 = covariantJetNormSq (I := I) (M := M) g 2 W := by
      simpa only [D] using Real.sq_sqrt hW
    calc
      covariantJetNormSq (I := I) (M := M) g 1
          (A.firstOrderAction (I := I) (M := M) W) ≤
        (Cl * B * D) ^ 2 :=
          hlow A W B D hB hD hcoeff (by rw [hDsq])
      _ ≤ (C * B * D) ^ 2 := by
        exact pow_le_pow_left₀
          (mul_nonneg (mul_nonneg hCl hB) hD)
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left hCh) hB) hD) 2
      _ = Q * covariantJetNormSq (I := I) (M := M) g 2 W := by
        rw [show (C * B * D) ^ 2 = (C * B) ^ 2 * D ^ 2 by ring,
          hDsq]
  exact ⟨Q, hQ, hHi, hLo⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderAction_jet_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderAction_jet_bound target :: scope.openDecls } }

theorem first_order_action_sobolev_extensions_commute
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g) :
    (tensorHsInclusion (I := I) (M := M) (g := g)
        (r := 0) (s := 2) (show (1 : ℝ) ≤ 2 by norm_num)).comp
          (A.firstOrderActionThirdToSecondOrder (I := I) (M := M)) =
      (A.firstOrderActionSecondToFirstOrder (I := I) (M := M)).comp
        (tensorHsInclusion (I := I) (M := M) (g := g)
          (r := 0) (s := 2) (show (2 : ℝ) ≤ 3 by norm_num)) := by
  obtain ⟨_, _, hpair⟩ := exists_firstOrderAction_spectralSobolev_extensions (I := I) (M := M) g
  obtain ⟨Q, hQ, hHi, hLo⟩ := firstOrderAction_jet_bound (I := I) (M := M) hDim g A
  exact (hpair A Q hQ hHi hLo).2.2.2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.first_order_action_sobolev_extensions_commute then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.first_order_action_sobolev_extensions_commute"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.first_order_action_sobolev_extensions_commute ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.first_order_action_sobolev_extensions_commute

theorem firstOrderActionThirdToSecondOrder_apply
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g)
    (W : SmoothCcTensor g 0 2) :
    A.firstOrderActionThirdToSecondOrder (I := I) (M := M)
        (ccTensorToHs (I := I) (M := M) g 2 (3 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ)
        (A.firstOrderAction (I := I) (M := M) W) := by
  obtain ⟨_, _, hpair⟩ := exists_firstOrderAction_spectralSobolev_extensions (I := I) (M := M) g
  obtain ⟨Q, hQ, hHi, hLo⟩ := firstOrderAction_jet_bound (I := I) (M := M) hDim g A
  exact (hpair A Q hQ hHi hLo).2.2.1 W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionThirdToSecondOrder_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionThirdToSecondOrder_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionThirdToSecondOrder_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionThirdToSecondOrder_apply

theorem firstOrderActionSecondToFirstOrder_apply
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A : LowerScaleActionCoefficients g)
    (W : SmoothCcTensor g 0 2) :
    A.firstOrderActionSecondToFirstOrder (I := I) (M := M)
        (ccTensorToHs (I := I) (M := M) g 2 (2 : ℝ) W) =
      ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ)
        (A.firstOrderAction (I := I) (M := M) W) := by
  obtain ⟨_, _, hpair⟩ := exists_firstOrderAction_spectralSobolev_extensions (I := I) (M := M) g
  obtain ⟨Q, hQ, hHi, hLo⟩ := firstOrderAction_jet_bound (I := I) (M := M) hDim g A
  exact (hpair A Q hQ hHi hLo).2.2.2.1 W

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionSecondToFirstOrder_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionSecondToFirstOrder_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionSecondToFirstOrder_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionSecondToFirstOrder_apply

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem firstOrderAction_add_core
    (g : SmoothRiemannianMetric I M) (A B F : LowerScaleActionCoefficients g)
    (h0 : F.zeroOrderCoefficient = A.zeroOrderCoefficient + B.zeroOrderCoefficient) (h1 : F.firstOrderCoefficient = A.firstOrderCoefficient + B.firstOrderCoefficient)
    (W : SmoothCcTensor g 0 2) :
    F.firstOrderAction (I := I) (M := M) W =
      A.firstOrderAction (I := I) (M := M) W + B.firstOrderAction (I := I) (M := M) W := by
  simp only [LowerScaleActionCoefficients.firstOrderAction, h0, h1, operatorFieldApplication_add_left]
  abel

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderAction_add_core
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderAction_add_core target :: scope.openDecls } }

theorem firstOrderActionThirdToSecondOrder_add
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A B F : LowerScaleActionCoefficients g)
    (h0 : F.zeroOrderCoefficient = A.zeroOrderCoefficient + B.zeroOrderCoefficient) (h1 : F.firstOrderCoefficient = A.firstOrderCoefficient + B.firstOrderCoefficient) :
    F.firstOrderActionThirdToSecondOrder (I := I) (M := M) =
      A.firstOrderActionThirdToSecondOrder (I := I) (M := M) + B.firstOrderActionThirdToSecondOrder (I := I) (M := M) := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (3 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)
  apply ContinuousLinearMap.ext
  intro x
  refine hdense.induction_on x
    (isClosed_eq (F.firstOrderActionThirdToSecondOrder (I := I) (M := M)).continuous
      (A.firstOrderActionThirdToSecondOrder (I := I) (M := M) +
        B.firstOrderActionThirdToSecondOrder (I := I) (M := M)).continuous) ?_
  intro W
  rw [ccToHsLin_apply, add_apply,
    firstOrderActionThirdToSecondOrder_apply (I := I) (M := M) hDim g F W,
    firstOrderActionThirdToSecondOrder_apply (I := I) (M := M) hDim g A W,
    firstOrderActionThirdToSecondOrder_apply (I := I) (M := M) hDim g B W,
    firstOrderAction_add_core (I := I) (M := M) g A B F h0 h1 W,
    ccTensorToHs_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionThirdToSecondOrder_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionThirdToSecondOrder_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionThirdToSecondOrder_add ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionThirdToSecondOrder_add

theorem firstOrderActionSecondToFirstOrder_add
    (hDim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric I M) (A B F : LowerScaleActionCoefficients g)
    (h0 : F.zeroOrderCoefficient = A.zeroOrderCoefficient + B.zeroOrderCoefficient) (h1 : F.firstOrderCoefficient = A.firstOrderCoefficient + B.firstOrderCoefficient) :
    F.firstOrderActionSecondToFirstOrder (I := I) (M := M) =
      A.firstOrderActionSecondToFirstOrder (I := I) (M := M) + B.firstOrderActionSecondToFirstOrder (I := I) (M := M) := by
  have hdense : DenseRange
      (ccToHsLin (I := I) (M := M) g 2 (2 : ℝ)) :=
    ccToHsLin_dense (I := I) (M := M) g 2 (by norm_num)
  apply ContinuousLinearMap.ext
  intro x
  refine hdense.induction_on x
    (isClosed_eq (F.firstOrderActionSecondToFirstOrder (I := I) (M := M)).continuous
      (A.firstOrderActionSecondToFirstOrder (I := I) (M := M) +
        B.firstOrderActionSecondToFirstOrder (I := I) (M := M)).continuous) ?_
  intro W
  rw [ccToHsLin_apply, add_apply,
    firstOrderActionSecondToFirstOrder_apply (I := I) (M := M) hDim g F W,
    firstOrderActionSecondToFirstOrder_apply (I := I) (M := M) hDim g A W,
    firstOrderActionSecondToFirstOrder_apply (I := I) (M := M) hDim g B W,
    firstOrderAction_add_core (I := I) (M := M) g A B F h0 h1 W,
    ccTensorToHs_add]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionSecondToFirstOrder_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionSecondToFirstOrder_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionSecondToFirstOrder_add ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.firstOrderActionSecondToFirstOrder_add

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry
