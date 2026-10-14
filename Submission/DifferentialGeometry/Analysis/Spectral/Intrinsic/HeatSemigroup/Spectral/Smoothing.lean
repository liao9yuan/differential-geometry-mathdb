import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.HeatSemigroup.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation.Smoothing.Sobolev
import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.CovariantDerivative.Cm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev.SmoothCcTensorHs
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Spectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

theorem tensorL2Coeff_tensorHeatSemigroup
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {t : ℝ} (ht : 0 ≤ t) (u₀ : TensorL2 r s g)
    (i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        (tensorHeatSemigroup (I := I) (M := M) g r s t u₀) i =
      Real.exp (-(TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          u₀ i := by
  rw [tensorL2Coeff_eq_inner, tensorL2Coeff_eq_inner]
  exact tensorHeatSemigroup_inner_eigenbasis
    (I := I) (M := M) g r s ht u₀ i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_tensorHeatSemigroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_tensorHeatSemigroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_tensorHeatSemigroup ``Submission.DifferentialGeometry.Analysis.Spectral.tensorL2Coeff_tensorHeatSemigroup

private def baseHZero (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u₀ : TensorL2 r s g) :
    TensorHs (I := I) (M := M) g r s 0 :=
  (tensorHsZeroEquivL2 (I := I) (M := M)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)).symm u₀

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.baseHZero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.baseHZero target :: scope.openDecls } }

private lemma baseHZero_coeff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (u₀ : TensorL2 r s g) (i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    (baseHZero (I := I) (M := M) g r s u₀).coeff i =
      tensorL2Coeff (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        u₀ i :=
  tensorHsZeroEquivL2_symm_coeff (I := I) (M := M) _ u₀ i

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.baseHZero_coeff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.baseHZero_coeff target :: scope.openDecls } }

def tensorHeatSemigroupHs (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : ℝ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    TensorHs (I := I) (M := M) g r s σ :=
  TensorHs.heatHsFun (I := I) (M := M) σ ht
    (baseHZero (I := I) (M := M) g r s u₀)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroupHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroupHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroupHs ``Submission.DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroupHs

@[simp] theorem tensorHeatSemigroupHs_coeff (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (σ : ℝ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g)
    (i : TensorHeatEquation.TensorEigenIdx (I := I) (M := M) g r s) :
    (tensorHeatSemigroupHs (I := I) (M := M) g r s σ ht u₀).coeff i =
      Real.exp (-(TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
        tensorL2Coeff (I := I) (M := M)
          (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
          u₀ i := by
  unfold tensorHeatSemigroupHs
  rw [TensorHs.heatHsFun_coeff, baseHZero_coeff]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroupHs_coeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroupHs_coeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroupHs_coeff ``Submission.DifferentialGeometry.Analysis.Spectral.tensorHeatSemigroupHs_coeff

theorem heat_semigroup_into_tensorHs (g : SmoothRiemannianMetric I M) (r s : ℕ)
    {σ : ℝ} (hσ : 0 ≤ σ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)
        hσ (tensorHeatSemigroupHs (I := I) (M := M) g r s σ ht u₀) =
      tensorHeatSemigroup (I := I) (M := M) g r s t u₀ := by
  set h_compact :=
    tensorResolventL2_isCompactOperator (I := I) (M := M) g r s
    with hcompact_def
  refine (tensorResolventHilbertEigenbasisSigma
    (I := I) (M := M) h_compact).repr.injective ?_
  ext i
  have hlhs :
      ((tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_compact).repr
        (tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
          h_compact hσ (tensorHeatSemigroupHs (I := I) (M := M) g r s σ ht u₀))) i =
        Real.exp (-(TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          tensorL2Coeff (I := I) (M := M) h_compact u₀ i := by
    have h := tensorHsToL2_tensorL2Coeff
      (I := I) (M := M) (h_compact := h_compact) hσ
      (tensorHeatSemigroupHs (I := I) (M := M) g r s σ ht u₀) i
    rw [tensorHeatSemigroupHs_coeff] at h
    simpa only [tensorL2Coeff] using h
  have hrhs :
      ((tensorResolventHilbertEigenbasisSigma
          (I := I) (M := M) h_compact).repr
        (tensorHeatSemigroup (I := I) (M := M) g r s t u₀)) i =
        Real.exp (-(TensorHeatEquation.TensorEigenIdx.lambda (I := I) (M := M) i) * t) *
          tensorL2Coeff (I := I) (M := M) h_compact u₀ i := by
    have h := tensorL2Coeff_tensorHeatSemigroup
      (I := I) (M := M) g r s ht.le u₀ i
    simpa only [tensorL2Coeff] using h
  rw [hlhs, hrhs]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.heat_semigroup_into_tensorHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.heat_semigroup_into_tensorHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.heat_semigroup_into_tensorHs ``Submission.DifferentialGeometry.Analysis.Spectral.heat_semigroup_into_tensorHs

theorem heat_semigroup_into_all_tensorHs (g : SmoothRiemannianMetric I M)
    (r s : ℕ) {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    ∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : TensorHs (I := I) (M := M) g r s σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) g r s) hσ v =
          tensorHeatSemigroup (I := I) (M := M) g r s t u₀ :=
  fun σ hσ =>
    ⟨tensorHeatSemigroupHs (I := I) (M := M) g r s σ ht u₀,
      heat_semigroup_into_tensorHs (I := I) (M := M) g r s hσ ht u₀⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.heat_semigroup_into_all_tensorHs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.heat_semigroup_into_all_tensorHs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.heat_semigroup_into_all_tensorHs ``Submission.DifferentialGeometry.Analysis.Spectral.heat_semigroup_into_all_tensorHs

def SpectralSmoothRealizesAsSmooth (g : SmoothRiemannianMetric I M)
    (r s : ℕ) : Prop :=
  ∀ u : TensorL2 r s g,
    (∀ σ : ℝ, ∀ hσ : 0 ≤ σ,
      ∃ v : TensorHs (I := I) (M := M) g r s σ,
        tensorHsToL2 (I := I) (M := M) (g := g) (r := r) (s := s)
            (tensorResolventL2_isCompactOperator
              (I := I) (M := M) g r s) hσ v = u) →
    ∃ T : SmoothCcTensor g r s, (T : TensorL2 r s g) = u

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.SpectralSmoothRealizesAsSmooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.SpectralSmoothRealizesAsSmooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.SpectralSmoothRealizesAsSmooth ``Submission.DifferentialGeometry.Analysis.Spectral.SpectralSmoothRealizesAsSmooth

theorem spectral_smooth_realization_reduction
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (h_gate : SpectralSmoothRealizesAsSmooth (I := I) (M := M) g r s)
    {t : ℝ} (ht : 0 < t) (u₀ : TensorL2 r s g) :
    ∃ T : SmoothCcTensor g r s,
      (T : TensorL2 r s g) =
        tensorHeatSemigroup (I := I) (M := M) g r s t u₀ :=
  h_gate _ (fun σ hσ =>
    ⟨tensorHeatSemigroupHs (I := I) (M := M) g r s σ ht u₀,
      heat_semigroup_into_tensorHs (I := I) (M := M) g r s hσ ht u₀⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.spectral_smooth_realization_reduction then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.spectral_smooth_realization_reduction"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.spectral_smooth_realization_reduction ``Submission.DifferentialGeometry.Analysis.Spectral.spectral_smooth_realization_reduction

end Spectral
end Analysis
end DifferentialGeometry

end
