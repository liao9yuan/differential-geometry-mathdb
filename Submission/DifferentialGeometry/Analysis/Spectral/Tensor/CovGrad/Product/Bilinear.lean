import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Iterated.Linear
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Defs
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.OperatorField.Bounds.SingleSlotFiberNorm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Tensor.RicciIdentity
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators _root_.Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance tensorRSRiemannianNormedAddCommGroup_local
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M ↦ Tensor0SBundle.TensorRSSpace r s I b)]
    (b : M) : NormedAddCommGroup (Tensor0SBundle.TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.tensorRSRiemannianNormedAddCommGroup_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.tensorRSRiemannianNormedAddCommGroup_local target :: scope.openDecls } }

omit [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem covGrad_heq_congr (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) :
    HEq (covGrad g r a Y) (covGrad g r b Z) := by
  subst h
  rw [eq_of_heq hYZ]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.covGrad_heq_congr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.covGrad_heq_congr target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
private theorem iteratedCovGrad_covGrad_comm_heq (g : SmoothRiemannianMetric I M) (r s m : ℕ)
    (X : SmoothCcTensor g r s) :
    HEq (iteratedCovGrad g r (s + 1) m (covGrad g r s X))
      (iteratedCovGrad g r s (m + 1) X) := by
  induction m with
  | zero =>
      rw [iteratedCovGrad_zero, iteratedCovGrad_succ, iteratedCovGrad_zero]
      exact HEq.rfl
  | succ k ih =>
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s + 1) (j := k) (covGrad g r s X)]
      rw [iteratedCovGrad_succ (g := g) (r := r) (s := s) (j := k + 1) X]
      exact covGrad_heq_congr g r (by omega : (s + 1) + k = s + (k + 1)) ih

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_covGrad_comm_heq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.iteratedCovGrad_covGrad_comm_heq target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem norm_toSection_heq_congr (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ}
    (h : a = b) {Y : SmoothCcTensor g r a} {Z : SmoothCcTensor g r b} (hYZ : HEq Y Z) (x : M) :
    ‖Y.toSection x‖ = ‖Z.toSection x‖ := by
  subst h
  rw [eq_of_heq hYZ]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.norm_toSection_heq_congr
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.norm_toSection_heq_congr target :: scope.openDecls } }

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem norm_toSection_iteratedCovGrad_covGrad_comm (g : SmoothRiemannianMetric I M)
    (r s m : ℕ) (X : SmoothCcTensor g r s) (x : M) :
    ‖(iteratedCovGrad g r (s + 1) m (covGrad g r s X)).toSection x‖ =
      ‖(iteratedCovGrad g r s (m + 1) X).toSection x‖ :=
  norm_toSection_heq_congr g r (by omega : (s + 1) + m = s + (m + 1))
    (iteratedCovGrad_covGrad_comm_heq (g := g) (r := r) (s := s) (m := m) X) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.norm_toSection_iteratedCovGrad_covGrad_comm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.norm_toSection_iteratedCovGrad_covGrad_comm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.norm_toSection_iteratedCovGrad_covGrad_comm ``Submission.DifferentialGeometry.Analysis.Spectral.norm_toSection_iteratedCovGrad_covGrad_comm

def castRankCc (g : SmoothRiemannianMetric I M) (r : ℕ) {a b : ℕ} (h : a = b)
    (Y : SmoothCcTensor g r a) : SmoothCcTensor g r b :=
  h ▸ Y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.castRankCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.castRankCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.castRankCc ``Submission.DifferentialGeometry.Analysis.Spectral.castRankCc

omit [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem norm_toSection_iteratedCovGrad_castRankCc (g : SmoothRiemannianMetric I M) (r : ℕ)
    {a b : ℕ} (h : a = b) (Y : SmoothCcTensor g r a) (j : ℕ) (x : M) :
    ‖(iteratedCovGrad g r b j (castRankCc g r h Y)).toSection x‖ =
      ‖(iteratedCovGrad g r a j Y).toSection x‖ := by
  subst h
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.norm_toSection_iteratedCovGrad_castRankCc then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.norm_toSection_iteratedCovGrad_castRankCc"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.norm_toSection_iteratedCovGrad_castRankCc ``Submission.DifferentialGeometry.Analysis.Spectral.norm_toSection_iteratedCovGrad_castRankCc

structure ParallelTensorProduct (g : SmoothRiemannianMetric I M) (r₁ s₁ r₂ s₂ r₀ s₀ : ℕ) where
  prod : ∀ {a b : ℕ}, SmoothCcTensor g r₁ (s₁ + a) → SmoothCcTensor g r₂ (s₂ + b) →
    SmoothCcTensor g r₀ (s₀ + a + b)
  opNorm : ℝ
  opNorm_nonneg : 0 ≤ opNorm
  riemannianFiberNormSq_prod_le : ∀ {a b : ℕ} (S : SmoothCcTensor g r₁ (s₁ + a)) (T : SmoothCcTensor g r₂ (s₂ + b))
    (x : M),
    riemannianFiberNormSq (I := I) (M := M) g r₀ (s₀ + a + b) x ((prod S T).toSection x) ≤
      opNorm * riemannianFiberNormSq (I := I) (M := M) g r₁ (s₁ + a) x (S.toSection x) *
        riemannianFiberNormSq (I := I) (M := M) g r₂ (s₂ + b) x (T.toSection x)
  covGrad_prod : ∀ {a b : ℕ} (S : SmoothCcTensor g r₁ (s₁ + a)) (T : SmoothCcTensor g r₂ (s₂ + b)),
    covGrad g r₀ (s₀ + a + b) (prod S T) =
      castRankCc g r₀ (by omega : s₀ + (a + 1) + b = s₀ + a + b + 1)
          (prod (a := a + 1) (b := b) (covGrad g r₁ (s₁ + a) S) T) +
        prod (a := a) (b := b + 1) S (covGrad g r₂ (s₂ + b) T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ParallelTensorProduct then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ParallelTensorProduct"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ParallelTensorProduct ``Submission.DifferentialGeometry.Analysis.Spectral.ParallelTensorProduct

namespace ParallelTensorProduct

variable {g : SmoothRiemannianMetric I M} {r₁ s₁ r₂ s₂ r₀ s₀ : ℕ}

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] [SigmaCompactSpace M] in
private theorem eq_zero_of_riemannianFiberNormSq_eq_zero (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (x : M) (z : Tensor0SBundle.TensorRSSpace r s I x)
    (hz : riemannianFiberNormSq (I := I) (M := M) g r s x z = 0) : z = 0 := by
  let : Bundle.RiemannianBundle (fun b : M => Tensor0SBundle.TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
  have hnorm_sq : ‖z‖ ^ 2 = 0 :=
    (riemannianFiberNormSq_eq_bundle_norm_sq (I := I) (M := M) g r s x z).symm.trans hz
  have hnorm : ‖z‖ = 0 := by nlinarith [norm_nonneg z, hnorm_sq]
  exact norm_eq_zero.mp hnorm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.ParallelTensorProduct.eq_zero_of_riemannianFiberNormSq_eq_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.ParallelTensorProduct.eq_zero_of_riemannianFiberNormSq_eq_zero target :: scope.openDecls } }

omit [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem prod_zero_left (Φ : ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀) {a b : ℕ}
    (T : SmoothCcTensor g r₂ (s₂ + b)) :
    Φ.prod (0 : SmoothCcTensor g r₁ (s₁ + a)) T = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hle := Φ.riemannianFiberNormSq_prod_le (0 : SmoothCcTensor g r₁ (s₁ + a)) T x
  have hzero : ((0 : SmoothCcTensor g r₁ (s₁ + a)).toSection x) = 0 := by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl
  rw [hzero, riemannianFiberNormSq_zero, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul] at hle
  have hval : (Φ.prod (0 : SmoothCcTensor g r₁ (s₁ + a)) T).toSection x = 0 :=
    eq_zero_of_riemannianFiberNormSq_eq_zero (I := I) g r₀ (s₀ + a + b) x _
      (le_antisymm hle (riemannianFiberNormSq_nonneg (I := I) (M := M) g r₀ (s₀ + a + b) x _))
  rw [show ((0 : SmoothCcTensor g r₀ (s₀ + a + b)).toSection x) = 0 from by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]
  exact hval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ParallelTensorProduct.prod_zero_left then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ParallelTensorProduct.prod_zero_left"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ParallelTensorProduct.prod_zero_left ``Submission.DifferentialGeometry.Analysis.Spectral.ParallelTensorProduct.prod_zero_left

omit [CompactSpace M] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem prod_zero_right (Φ : ParallelTensorProduct g r₁ s₁ r₂ s₂ r₀ s₀) {a b : ℕ}
    (S : SmoothCcTensor g r₁ (s₁ + a)) :
    Φ.prod S (0 : SmoothCcTensor g r₂ (s₂ + b)) = 0 := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  have hle := Φ.riemannianFiberNormSq_prod_le S (0 : SmoothCcTensor g r₂ (s₂ + b)) x
  have hzero : ((0 : SmoothCcTensor g r₂ (s₂ + b)).toSection x) = 0 := by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl
  rw [hzero, riemannianFiberNormSq_zero, _root_.MulZeroClass.mul_zero] at hle
  have hval : (Φ.prod S (0 : SmoothCcTensor g r₂ (s₂ + b))).toSection x = 0 :=
    eq_zero_of_riemannianFiberNormSq_eq_zero (I := I) g r₀ (s₀ + a + b) x _
      (le_antisymm hle (riemannianFiberNormSq_nonneg (I := I) (M := M) g r₀ (s₀ + a + b) x _))
  rw [show ((0 : SmoothCcTensor g r₀ (s₀ + a + b)).toSection x) = 0 from by
    rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]
  exact hval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.ParallelTensorProduct.prod_zero_right then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.ParallelTensorProduct.prod_zero_right"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.ParallelTensorProduct.prod_zero_right ``Submission.DifferentialGeometry.Analysis.Spectral.ParallelTensorProduct.prod_zero_right

end ParallelTensorProduct

end Spectral
end Analysis
end DifferentialGeometry

end
