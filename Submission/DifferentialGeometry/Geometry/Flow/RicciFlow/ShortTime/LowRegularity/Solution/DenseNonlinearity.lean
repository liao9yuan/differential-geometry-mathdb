import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothInjectivity
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SobolevNonlinearity.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.FixedPoint.PartialForcing
import Submission.DifferentialGeometry.Geometry.Metric.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Parabolic
    DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section

open _root_.Bundle _root_.Submission.Bundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M]

theorem smoothHs_inj (g : SmoothRiemannianMetric I M) (σ : ℝ) :
    Function.Injective (smoothCcToTensorHs (I := I) (M := M) g σ) := by
  intro S T hST
  apply ccToHs_injective (I := I) (M := M) g 2 σ
  apply TensorHs.ext
  funext i
  have hi := congrArg (fun u => u.coeff i) hST
  simpa only [ccTensorToHs_coeff, smoothCcToTensorHs_coeff] using hi

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.smoothHs_inj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.smoothHs_inj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.smoothHs_inj ``Submission.DifferentialGeometry.PDE.RicciFlow.smoothHs_inj

theorem deTurckSmoothRemainderTensorHs_eq_of_smoothCcToTensorHs_eq
    (g₀ g_bg : SmoothRiemannianMetric I M) (a : ℕ)
    (T T' : SmoothCcTensor g₀ 0 2)
    {δ : ℝ} (hδ_lt : δ < 1)
    (hδ : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T) δ)
    {δ' : ℝ} (hδ'_lt : δ' < 1)
    (hδ' : metricCauchySchwarzBound (I := I) (M := M) g₀
      (ccTensorBilinSymm (I := I) g₀ T') δ')
    (hTT' : smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T =
      smoothCcToTensorHs (I := I) (M := M) g₀ ((a : ℝ) + 2) T') :
    deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T hδ_lt hδ =
      deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg a T' hδ'_lt hδ' := by
  have hT : T = T' :=
    smoothHs_inj (I := I) (M := M) g₀ ((a : ℝ) + 2) hTT'
  subst T'
  have hg :
      tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ =
        tensorSectionRealizeMetric (I := I) g₀ T hδ'_lt hδ' := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [tensorSectionRealizeMetric_inner, tensorSectionRealizeMetric_inner]
  have hrem :
      deTurckSmoothRemainder (I := I) g₀ g_bg T hδ_lt hδ =
        deTurckSmoothRemainder (I := I) g₀ g_bg T hδ'_lt hδ' := by
    apply SmoothCcTensor.ext
    change
      (deTurckRHSSection (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ T hδ_lt hδ)).toSection -
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toSection =
        (deTurckRHSSection (I := I) g_bg
          (tensorSectionRealizeMetric (I := I) g₀ T hδ'_lt hδ')).toSection -
          (rawTensorConnLapSmooth (I := I) g₀ 0 2 T).toSection
    rw [hg]
  apply TensorHs.ext
  funext i
  rw [deTurckSmoothN_coeff, deTurckSmoothN_coeff, hrem]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckSmoothRemainderTensorHs_eq_of_smoothCcToTensorHs_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckSmoothRemainderTensorHs_eq_of_smoothCcToTensorHs_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckSmoothRemainderTensorHs_eq_of_smoothCcToTensorHs_eq ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckSmoothRemainderTensorHs_eq_of_smoothCcToTensorHs_eq

def smoothCore (g₀ : SmoothRiemannianMetric I M) (R : ℝ) :
    Set (lowerState (I := I) (M := M) g₀ 1 R) :=
  lowerCore
    (Set.range (smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)))
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)) R

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.smoothCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.smoothCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.smoothCore ``Submission.DifferentialGeometry.PDE.RicciFlow.smoothCore

theorem smoothCore_dense (g₀ : SmoothRiemannianMetric I M)
    {R : ℝ} (hR : 0 < R) : Dense (smoothCore (I := I) (M := M) g₀ R) := by
  exact dense_lowerCore
    (smoothCcToTensorHs_denseRange (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2))
    (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)) hR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.smoothCore_dense then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.smoothCore_dense"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.smoothCore_dense ``Submission.DifferentialGeometry.PDE.RicciFlow.smoothCore_dense

def coreRep (g₀ : SmoothRiemannianMetric I M) {R : ℝ}
    (x : smoothCore (I := I) (M := M) g₀ R) : SmoothCcTensor g₀ 0 2 :=
  Classical.choose x.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.coreRep then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.coreRep"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.coreRep ``Submission.DifferentialGeometry.PDE.RicciFlow.coreRep

theorem coreRep_spec (g₀ : SmoothRiemannianMetric I M) {R : ℝ}
    (x : smoothCore (I := I) (M := M) g₀ R) :
    smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2) (coreRep g₀ x) =
      (x.1.1 : TensorHs (I := I) (M := M) g₀ 0 2 (((1 : ℕ) : ℝ) + 2)) :=
  Classical.choose_spec x.property

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.coreRep_spec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.coreRep_spec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.coreRep_spec ``Submission.DifferentialGeometry.PDE.RicciFlow.coreRep_spec

theorem coreSymm_h2 (g₀ : SmoothRiemannianMetric I M) {R : ℝ}
    (x : smoothCore (I := I) (M := M) g₀ R) :
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1)
      (ccTensor02Symm (I := I) (M := M) g₀ (coreRep g₀ x))‖ ≤ R := by
  have hsymm := norm_smoothCcToTensorHs_ccTensor02Symm_le
    (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) (coreRep g₀ x)
  have hincl := tensorHsInclusion_smoothCcToTensorHs
    (I := I) (M := M) g₀
      (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith) (coreRep g₀ x)
  have hxR :
      ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith) (x.1.1)‖ ≤ R :=
    x.1.2
  calc
    ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1)
        (ccTensor02Symm (I := I) (M := M) g₀ (coreRep g₀ x))‖ ≤
        ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1)
          (coreRep g₀ x)‖ := hsymm
    _ = ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith)
          (smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 2)
            (coreRep g₀ x))‖ := by
      rw [hincl]
    _ = ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := 0) (s := 2)
        (show ((1 : ℕ) : ℝ) + 1 ≤ ((1 : ℕ) : ℝ) + 2 by linarith) (x.1.1)‖ := by
      rw [coreRep_spec]
    _ ≤ R := hxR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.coreSymm_h2 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.coreSymm_h2"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.coreSymm_h2 ``Submission.DifferentialGeometry.PDE.RicciFlow.coreSymm_h2

def deTurckRemainderOnSmoothCore (g₀ g_bg : SmoothRiemannianMetric I M) {R δ : ℝ} (hδ : δ < 1)
    (hreal : ∀ T : SmoothCcTensor g₀ 0 2,
      ‖smoothCcToTensorHs (I := I) (M := M) g₀ (((1 : ℕ) : ℝ) + 1) T‖ ≤ R →
        metricCauchySchwarzBound (I := I) (M := M) g₀
          (ccTensorBilinSymm (I := I) g₀ T) δ) :
    smoothCore (I := I) (M := M) g₀ R →
      TensorHs (I := I) (M := M) g₀ 0 2 ((1 : ℕ) : ℝ) :=
  fun x => deTurckSmoothRemainderTensorHs (I := I) (M := M) g₀ g_bg (1 : ℕ)
    (ccTensor02Symm (I := I) (M := M) g₀ (coreRep g₀ x)) hδ
    (hreal _ (coreSymm_h2 (I := I) (M := M) g₀ x))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.deTurckRemainderOnSmoothCore then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.deTurckRemainderOnSmoothCore"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.deTurckRemainderOnSmoothCore ``Submission.DifferentialGeometry.PDE.RicciFlow.deTurckRemainderOnSmoothCore

end DifferentialGeometry.PDE.RicciFlow

end
