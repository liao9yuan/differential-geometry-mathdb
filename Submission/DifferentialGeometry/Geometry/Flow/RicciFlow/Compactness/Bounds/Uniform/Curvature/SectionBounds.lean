import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.Curvature.JetDifference

import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Uniform.JetComparison.Tower
import Submission.DifferentialGeometry.Tensor.Mixed.Field

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Integral.Connection
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Tensor

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow

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


def smoothCompactTensorOfField (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s) :
    SmoothCcTensor g 0 s where
  toSection :=
    MixedSection.fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
      (E := (TangentSpace I : M → Type _)) ∞ A
  hasCompactSupport := HasCompactSupport.of_compactSpace _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.smoothCompactTensorOfField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.smoothCompactTensorOfField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.smoothCompactTensorOfField ``Submission.DifferentialGeometry.PDE.RicciFlow.smoothCompactTensorOfField


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
@[simp] theorem smoothCompactTensorOfField_unit (g : SmoothRiemannianMetric I M) (s : ℕ)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s) :
    ccUnitField (I := I) g s (smoothCompactTensorOfField (I := I) g s A) = A :=
  MixedSection.toMultilinearSection_fromMultilinearSection (𝕜 := ℝ) (F := E) (IB := I)
    (E := (TangentSpace I : M → Type _)) ∞ A

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.smoothCompactTensorOfField_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.smoothCompactTensorOfField_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.smoothCompactTensorOfField_unit ``Submission.DifferentialGeometry.PDE.RicciFlow.smoothCompactTensorOfField_unit

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_smoothCompactTensorOfField_eq (g : SmoothRiemannianMetric I M) (s j : ℕ)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s)
    (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + j) x
        ((iteratedCovGrad (I := I) g 0 s j (smoothCompactTensorOfField (I := I) g s A)).toSection x) =
      normSq0S (I := I) g x (s + j) (iterCov (I := I) g s A j x) := by
  rw [riemannianFiberNormSq_iterCovGrad_eq (I := I) g s j (smoothCompactTensorOfField (I := I) g s A) x, smoothCompactTensorOfField_unit]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq_smoothCompactTensorOfField_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq_smoothCompactTensorOfField_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq_smoothCompactTensorOfField_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq_smoothCompactTensorOfField_eq

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem zeroS_eq_unit (x : M) (D : Tensor0SSpace 0 I x) :
    D = (Tensor0SNabla.tensor0Iso I M x D) • (unitZeroSec (I := I) (M := M) x) := by
  classical
  have hunit :
      Tensor0SNabla.tensor0Iso I M x (unitZeroSec (I := I) (M := M) x) = (1 : ℝ) := by
    have h := Tensor0SNabla.scalarFn_unitZero (I := I) (M := M)
    have hx := congrFun h x
    simpa [Tensor0SNabla.scalarFn_apply, unitZeroSec_apply] using hx
  apply (Tensor0SNabla.tensor0Iso I M x).injective
  rw [map_smul, hunit, smul_eq_mul, mul_one]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.zeroS_eq_unit
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.zeroS_eq_unit target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem rs0_apply_eq_smul {s : ℕ} (x : M)
    (Φ : Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x) (D : Tensor0SSpace 0 I x) :
    Φ D = (Tensor0SNabla.tensor0Iso I M x D) • Φ (unitZeroSec (I := I) (M := M) x) := by
  conv_lhs => rw [zeroS_eq_unit (I := I) (M := M) x D]
  rw [map_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.rs0_apply_eq_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.rs0_apply_eq_smul target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
theorem smoothCompactTensor_ext_unitField (g : SmoothRiemannianMetric I M) {s : ℕ}
    (W₁ W₂ : SmoothCcTensor g 0 s)
    (h : ∀ x : M, ccUnitField (I := I) g s W₁ x = ccUnitField (I := I) g s W₂ x) :
    W₁ = W₂ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext
  intro D
  rw [rs0_apply_eq_smul (I := I) (M := M) x
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W₁.toSection x) D,
    rs0_apply_eq_smul (I := I) (M := M) x
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from W₂.toSection x) D]
  exact congrArg _ (h x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.smoothCompactTensor_ext_unitField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.smoothCompactTensor_ext_unitField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.smoothCompactTensor_ext_unitField ``Submission.DifferentialGeometry.PDE.RicciFlow.smoothCompactTensor_ext_unitField

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem iterCovGrad_smoothCompactTensorOfField (g : SmoothRiemannianMetric I M) (s j : ℕ)
    (A : Tensor0SBundle.Tensor0SField (𝕜 := ℝ) (E := E) (H := H) (I := I) (M := M) ∞ s) :
    iteratedCovGrad (I := I) g 0 s j (smoothCompactTensorOfField (I := I) g s A) =
      smoothCompactTensorOfField (I := I) g (s + j) (iterCov (I := I) g s A j) := by
  refine smoothCompactTensor_ext_unitField (I := I) g _ _ (fun x => ?_)
  have hL := congrFun
    (iterCovGrad_unit_eq (I := I) g s (smoothCompactTensorOfField (I := I) g s A) j) x
  rw [smoothCompactTensorOfField_unit (I := I) g s A] at hL
  have hR : ccUnitField (I := I) g (s + j)
      (smoothCompactTensorOfField (I := I) g (s + j) (iterCov (I := I) g s A j)) x =
      iterCov (I := I) g s A j x := by
    rw [smoothCompactTensorOfField_unit (I := I) g (s + j) (iterCov (I := I) g s A j)]
  rw [hR]
  exact hL

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.iterCovGrad_smoothCompactTensorOfField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.iterCovGrad_smoothCompactTensorOfField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.iterCovGrad_smoothCompactTensorOfField ``Submission.DifferentialGeometry.PDE.RicciFlow.iterCovGrad_smoothCompactTensorOfField


def riemannCurvatureSection (g : SmoothRiemannianMetric I M) : SmoothCcTensor g 0 4 :=
  smoothCompactTensorOfField (I := I) g 4 (metricRm04 (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.riemannCurvatureSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.riemannCurvatureSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.riemannCurvatureSection ``Submission.DifferentialGeometry.PDE.RicciFlow.riemannCurvatureSection


omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M] [SigmaCompactSpace M] in
@[simp] theorem riemannCurvatureSection_unit (g : SmoothRiemannianMetric I M) :
    ccUnitField (I := I) g 4 (riemannCurvatureSection (I := I) (M := M) g) =
      metricRm04 (I := I) (M := M) g :=
  smoothCompactTensorOfField_unit (I := I) g 4 (metricRm04 (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.riemannCurvatureSection_unit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.riemannCurvatureSection_unit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.riemannCurvatureSection_unit ``Submission.DifferentialGeometry.PDE.RicciFlow.riemannCurvatureSection_unit

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem riemannianFiberNormSq_riemannCurvatureSection_eq (g : SmoothRiemannianMetric I M) (j : ℕ) (x : M) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
        ((iteratedCovGrad (I := I) g 0 4 j (riemannCurvatureSection (I := I) (M := M) g)).toSection x) =
      normSq0S (I := I) g x (4 + j)
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) j x) :=
  riemannianFiberNormSq_smoothCompactTensorOfField_eq (I := I) g 4 j (metricRm04 (I := I) (M := M) g) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq_riemannCurvatureSection_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq_riemannCurvatureSection_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq_riemannCurvatureSection_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.riemannianFiberNormSq_riemannCurvatureSection_eq

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem iterCovGrad_riemannCurvatureSection (g : SmoothRiemannianMetric I M) (a : ℕ) :
    iteratedCovGrad (I := I) g 0 4 a (riemannCurvatureSection (I := I) (M := M) g) =
      smoothCompactTensorOfField (I := I) g (4 + a)
        (iterCov (I := I) g 4 (metricRm04 (I := I) (M := M) g) a) :=
  iterCovGrad_smoothCompactTensorOfField (I := I) g 4 a (metricRm04 (I := I) (M := M) g)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.iterCovGrad_riemannCurvatureSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.iterCovGrad_riemannCurvatureSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.iterCovGrad_riemannCurvatureSection ``Submission.DifferentialGeometry.PDE.RicciFlow.iterCovGrad_riemannCurvatureSection

private theorem sqLeOfSqrtLe {a K : ℝ} (ha : 0 ≤ a) (h : Real.sqrt a ≤ K) :
    a ≤ K ^ 2 := by
  nlinarith [Real.sq_sqrt ha, Real.sqrt_nonneg a]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.sqLeOfSqrtLe
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.sqLeOfSqrtLe target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem exists_riemannCurvatureSection_jet_bound (g : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (4 + a) x
          ((iteratedCovGrad (I := I) g 0 4 a (riemannCurvatureSection (I := I) (M := M) g)).toSection x) ≤
        K ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := exists_curvJet_sup (I := I) (M := M) g a
  refine ⟨K, hK0, fun x => ?_⟩
  refine sqLeOfSqrtLe (riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 (4 + a) x _) ?_
  rw [riemannianFiberNormSq_riemannCurvatureSection_eq (I := I) g a x]
  exact hK x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_riemannCurvatureSection_jet_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_riemannCurvatureSection_jet_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_riemannCurvatureSection_jet_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_riemannCurvatureSection_jet_bound

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem exists_riemannCurvatureSection_jet_bounds (g : SmoothRiemannianMetric I M) (a : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ j ≤ a, ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g 0 (4 + j) x
          ((iteratedCovGrad (I := I) g 0 4 j (riemannCurvatureSection (I := I) (M := M) g)).toSection x) ≤
        K ^ 2 := by
  induction a with
  | zero =>
      obtain ⟨K, hK0, hK⟩ := exists_riemannCurvatureSection_jet_bound (I := I) (M := M) g 0
      refine ⟨K, hK0, fun j hj x => ?_⟩
      obtain rfl : j = 0 := Nat.le_zero.mp hj
      exact hK x
  | succ a ih =>
      obtain ⟨K, hK0, hK⟩ := ih
      obtain ⟨K', hK'0, hK'⟩ := exists_riemannCurvatureSection_jet_bound (I := I) (M := M) g (a + 1)
      refine ⟨max K K', le_trans hK0 (le_max_left _ _), fun j hj x => ?_⟩
      rcases eq_or_lt_of_le hj with rfl | hlt
      · have hmono : K' ^ 2 ≤ _root_.Max.max K K' ^ 2 := by nlinarith [le_max_right K K']
        exact le_trans (hK' x) hmono
      · have hmono : K ^ 2 ≤ _root_.Max.max K K' ^ 2 := by nlinarith [le_max_left K K']
        exact le_trans (hK j (Nat.lt_succ_iff.mp hlt) x) hmono

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_riemannCurvatureSection_jet_bounds then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_riemannCurvatureSection_jet_bounds"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_riemannCurvatureSection_jet_bounds ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_riemannCurvatureSection_jet_bounds


omit [SigmaCompactSpace M] in
theorem exists_uniform_riemannCurvatureSection_bound
    (gBase g₀ : SmoothRiemannianMetric I M) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (hcomp : ∀ (x : M) (v : TangentSpace I x),
      Λ⁻¹ * gBase.inner x v v ≤ g₀.inner x v v ∧
        g₀.inner x v v ≤ Λ * gBase.inner x v v)
    (hjet1 : MetricCovDerivOrderBoundOn (I := I) Set.univ 1 g₀ gBase Λ)
    (hjet2 : MetricCovDerivOrderBoundOn (I := I) Set.univ 2 g₀ gBase Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
          ((riemannCurvatureSection (I := I) (M := M) g₀).toSection x) ≤ C ^ 2 := by
  obtain ⟨C, hC0, hC⟩ :=
    uniformRm04Sup (I := I) (M := M) gBase g₀ hΛ hcomp hjet1 hjet2
  refine ⟨C, hC0, fun x => ?_⟩
  have hkey : riemannianFiberNormSq (I := I) (M := M) g₀ 0 4 x
        ((riemannCurvatureSection (I := I) (M := M) g₀).toSection x) =
      normSq0S (I := I) g₀ x 4 (metricRm04 (I := I) (M := M) g₀ x) :=
    riemannianFiberNormSq_riemannCurvatureSection_eq (I := I) g₀ 0 x
  refine sqLeOfSqrtLe (riemannianFiberNormSq_nonneg (I := I) (M := M) g₀ 0 4 x _) ?_
  rw [hkey]
  exact hC x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_uniform_riemannCurvatureSection_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_uniform_riemannCurvatureSection_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_uniform_riemannCurvatureSection_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_uniform_riemannCurvatureSection_bound

end RicciFlow
end PDE
end DifferentialGeometry
