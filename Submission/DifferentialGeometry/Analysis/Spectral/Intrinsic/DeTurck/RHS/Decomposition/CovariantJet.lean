import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.RHS.Decomposition.AtZero
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHS.CovariantJetCancellation
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.RHS.PathIntegral
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.CovariantJetDecomposition.JointAlgebra

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.BigOperators _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral

open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

def rhsDecompositionTop
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ}
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (s : ℝ) : SmoothCcTensor g 4 2 :=
  rhsDecomposition2 (I := I) (M := M) g T hδ hδZ s +
    deTurckMetricPrincipalDefectTotal (I := I) (M := M) g
      (metricPerturbationPath (I := I) g T 0 hδ hδZ s)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rhsDecompositionTop then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rhsDecompositionTop"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rhsDecompositionTop ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rhsDecompositionTop

theorem lieDecomposition2_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g 4
      (lieDecomposition2 (I := I) (M := M) g T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  classical
  let a := 2 * Module.finrank ℝ E + 10
  let R : ℝ :=
    Finset.sum (Finset.range (a + 3))
      (fun j => ‖iteratedCovGrad (I := I) g 0 2 j T‖)
  have ha : 2 * Module.finrank ℝ E + 10 ≤ a := by
    simp [a]
  have hR : 0 ≤ R := by
    dsimp [R]
    exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hball :
      ∀ j : ℕ, j ≤ a + 2 →
        ‖iteratedCovGrad (I := I) g 0 2 j T‖ ≤ R := by
    intro j hj
    dsimp [R]
    exact Finset.single_le_sum
      (fun k _ => norm_nonneg (iteratedCovGrad (I := I) g 0 2 k T))
      (Finset.mem_range.mpr (by omega))
  have hε : ∀ i, |lieDecompositionEps i| ≤ 1 := by
    intro i
    fin_cases i <;> norm_num [lieDecompositionEps]
  obtain ⟨K, hK, hmain⟩ :=
    exists_deTurckLieCovariantDerivativeDecompositionC2Family_cap_l2JetWindow
      (I := I) (M := M) g a ha hR hδ_lt lieDecompositionQ lieDecompositionEps hε
  simpa only [linearizedRicciCovariantJetJointSmoothness, lieDecomposition2] using
    (hmain T le_rfl hδ hδZ hball).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lieDecomposition2_joint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lieDecomposition2_joint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lieDecomposition2_joint ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.lieDecomposition2_joint

theorem rhsDecompositionTop_joint
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ) :
    linearizedRicciCovariantJetJointSmoothness (I := I) (M := M) g 4
      (rhsDecompositionTop (I := I) (M := M) g T hδ hδZ)
      (δ := δ) (δ' := δ) := by
  have hRic0 :=
    riemannPalatiniDecompositionC2Family_covariantJetJointSmoothness
      (I := I) (M := M) g T hδ hδZ ricciDecompositionQA ricciDecompositionQB
  have hRic := covariantJetJoint_smul (I := I) (M := M) g (2 : ℝ) _ hRic0
  have hLie := lieDecomposition2_joint (I := I) (M := M) g T hδ_lt hδ hδZ
  have hDecomposition := covariantJetJoint_add (I := I) (M := M) g _ _ hRic hLie
  have hTop := rhs_top_path_joint (I := I) (M := M) g T 0 hδ hδZ
  have hAll := covariantJetJoint_add (I := I) (M := M) g _ _ hDecomposition hTop
  simpa only [linearizedRicciCovariantJetJointSmoothness, rhsDecompositionTop, rhsDecomposition2,
    ricciDecomposition2, lieDecomposition2] using hAll

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rhsDecompositionTop_joint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rhsDecompositionTop_joint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rhsDecompositionTop_joint ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rhsDecompositionTop_joint

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] in
private theorem zero_symm (g : SmoothRiemannianMetric I M) :
    ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x v w =
        ccTensorBilin (I := I) g (0 : SmoothCcTensor g 0 2) x w v := by
  intro x v w
  have h0 : (0 : SmoothCcTensor g 0 2) =
      (0 : ℝ) • (0 : SmoothCcTensor g 0 2) := (zero_smul ℝ _).symm
  rw [h0]
  simp only [ccTensorBilin_apply, ccTensorModel_smul,
    smul_apply, smul_eq_mul, _root_.MulZeroClass.zero_mul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.zero_symm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.zero_symm target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
theorem rhsSlope_decomposition
    (g g_bg : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2)
    (hT : ∀ (x : M) (v w : TangentSpace I x),
      ccTensorBilin (I := I) g T x v w =
        ccTensorBilin (I := I) g T x w v)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g T) δ)
    (hδZ : gFibreOpBound (I := I) (M := M) g
      (ccTensorBilinSymm (I := I) g (0 : SmoothCcTensor g 0 2)) δ)
    (x : M) (v w : TangentSpace I x) {s : ℝ} (hs : s ∈ _root_.Set.Ioo (0 : ℝ) 1) :
    rhsSumSlope (I := I) g g_bg T 0 hδ_lt hδ hδ_lt hδZ x v w s =
      unitModel (I := I) (M := M) g 2
        (operatorFieldApply (I := I) (M := M) g 2 2
            (rhsDecomposition0 (I := I) (M := M) g g_bg T hδ hδZ s) T +
          operatorFieldApply (I := I) (M := M) g 3 2
            (ricciDeTurckRemainderFirstOrderCoefficient (I := I) (M := M) g g_bg T 0 hδ hδZ s)
            (iteratedCovGrad (I := I) g 0 2 1 T) +
          operatorFieldApply (I := I) (M := M) g 4 2
            (rhsDecompositionTop (I := I) (M := M) g T hδ hδZ s)
            (iteratedCovGrad (I := I) g 0 2 2 T)) x
        ![tangentSpaceModelContinuousLinearEquiv (I := I) x v,
          tangentSpaceModelContinuousLinearEquiv (I := I) x w] := by
  rw [ricciDeTurckRemainderSlope_eq_terms (I := I) (M := M) g g_bg T 0 hT
    (zero_symm (I := I) (M := M) g) hδ_lt hδ hδ_lt hδZ x v w hs]
  simp only [sub_zero, iteratedCovGrad_zero]
  have hCoeff :
      DifferentialGeometry.Analysis.Spectral.DeTurckCoefficients.ricciDeTurckRemainderZeroOrderCoefficient
          (I := I) (M := M) g g_bg T 0 hδ hδZ s =
        DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.DeTurckCoefficients.ricciDeTurckRemainderZeroOrderCoefficient
          (I := I) (M := M) g g_bg T 0 hδ hδZ s := rfl
  rw [hCoeff]
  rw [rhsLow0_decomposition (I := I) (M := M) g g_bg T hT hδ_lt hδ hδZ
    ⟨le_of_lt hs.1, le_of_lt hs.2⟩]
  simp only [rhsDecompositionTop, operatorFieldApplication_add_left]
  apply congrArg (fun Z : SmoothCcTensor g 0 2 =>
    unitModel (I := I) (M := M) g 2 Z x
      ![tangentSpaceModelContinuousLinearEquiv (I := I) x v,
        tangentSpaceModelContinuousLinearEquiv (I := I) x w])
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rhsSlope_decomposition then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rhsSlope_decomposition"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rhsSlope_decomposition ``Submission.DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.rhsSlope_decomposition

end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
