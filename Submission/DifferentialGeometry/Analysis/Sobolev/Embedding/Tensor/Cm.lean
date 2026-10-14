import Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert.Hilbert.Defs
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.PouSobolevIso.SpectralPouH2Identify
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Embedding.Iterated
import Submission.DifferentialGeometry.Analysis.Sobolev.Manifold.Morrey.HigherOrder
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ChartComponent.ComponentSobolevBound
import Submission.DifferentialGeometry.Analysis.Sobolev.HebeyBlock.FiberNorm.FiberNormRiemannianBridge
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.Estimates.ComponentL2.TensorSection
import Submission.DifferentialGeometry.Analysis.Sobolev.Embedding.Tensor.ManifoldC0
import Mathlib.Geometry.Manifold.ContMDiff.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


namespace DifferentialGeometry.Analysis.Sobolev

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.IntrinsicSobolev

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

private noncomputable local instance tensorSobolevEmbeddingRiemannianNormedAddCommGroup
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.tensorSobolevEmbeddingRiemannianNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.tensorSobolevEmbeddingRiemannianNormedAddCommGroup target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tensorRSSpaceNormedAddCommGroup
  Tensor0SBundle.tensorRSSpaceNormedSpace in
omit [I.Boundaryless] in
omit [BoundarylessManifold I M] in
theorem tensorPouSobolevHilbert_embedding_Ck
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {r s k m : ℕ}
    (h_super : 2 * k > Module.finrank ℝ E + 2 * m) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRSRiemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 < C ∧
      ∀ (T : SmoothCcTensor g r s) (x : M),
        ‖T.toSection x‖ ≤
          C *
            ‖SmoothCcTensor.toHs (g := g) (r := r) (s := s) (2 * k) T‖ :=
  tensorPouSobolevHilbert_embedding_Ck_gNorm (I := I) (M := M) g r s k m h_super

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.tensorPouSobolevHilbert_embedding_Ck then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.tensorPouSobolevHilbert_embedding_Ck"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.tensorPouSobolevHilbert_embedding_Ck ``Submission.DifferentialGeometry.Analysis.Sobolev.tensorPouSobolevHilbert_embedding_Ck

end


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [BoundarylessManifold I M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

omit [BoundarylessManifold I M] [I.Boundaryless] in
theorem tensorChartComponentScalar_embedding_C0
    [I.Boundaryless]
    {g : SmoothRiemannianMetric I M} {r s k : ℕ}
    (hk : Module.finrank ℝ E < 2 * k)
    (hreg : DifferentialGeometry.Analysis.Sobolev.Chart.RegularExponent.IsRegular
      (Module.finrank ℝ E : ℝ) 2 k)
    (T : SmoothCcTensor g r s) (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ∃ (ũ : M → ℝ) (C : ℝ),
      Continuous ũ ∧ 0 ≤ C ∧
      (∀ᵐ x ∂(DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I) g
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I M)),
        ũ x =
          DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
            (I := I) (M := M) g r s T α Idx Jdx x) ∧
      (∀ x : M, ‖ũ x‖ ≤ C *
        (DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart (I := I) (M := M) k 2
          (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
            (I := I) (M := M) g r s T α Idx Jdx)).toReal) := by
  classical
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  have h_smooth :
      ContMDiff I 𝓘(ℝ, ℝ) ∞
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
          (I := I) (M := M) g r s T α Idx Jdx) :=
    DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar_contMDiff
      (I := I) (M := M) g r s T α Idx Jdx
  have h_meas :
      Measurable
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
          (I := I) (M := M) g r s T α Idx Jdx) :=
    h_smooth.continuous.measurable
  have h_mem :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart (I := I) (M := M) k 2
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentScalar
          (I := I) (M := M) g r s T α Idx Jdx) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.memWkpChart_of_contMDiff_k
      (I := I) (M := M) (p := 2) (by norm_num) k h_smooth
  exact DifferentialGeometry.Analysis.Sobolev.Chart.sobolev_embedding_chart_C0_Hk
    (I := I) (M := M) g hk hreg h_meas h_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.tensorChartComponentScalar_embedding_C0 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.tensorChartComponentScalar_embedding_C0"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.tensorChartComponentScalar_embedding_C0 ``Submission.DifferentialGeometry.Analysis.Sobolev.tensorChartComponentScalar_embedding_C0

omit [BoundarylessManifold I M] in
omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [T2Space M]
    [SigmaCompactSpace M] in
theorem tensorFiberNorm_sq_le_chartCenterComponents
    {g : SmoothRiemannianMetric I M} {r s : ℕ}
    (T : SmoothCcTensor g r s) (x : M) :
    ‖T.toSection x‖ ^ 2 ≤
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.midxPairCard
          (E := E) r s *
        (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartBasisNormConstant
          (E := E) r s) ^ 2 *
        ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
          ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
            (DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
              (I := I) (M := M) g r s T x Idx Jdx x) ^ 2 := by
  classical
  set Tmod : TensorRSModel r s ℝ E :=
    TensorRSSpace.toModel (𝕜 := ℝ) (I := I) (T.toSection x) with hTmod_def
  have h_norm_eq : ‖T.toSection x‖ = ‖Tmod‖ := rfl
  have h_raw_eq : ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
      (Jdx : Fin s → Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentProjection
          (E := E) r s Idx Jdx Tmod =
        DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw
          (I := I) (M := M) g r s T x Idx Jdx x := by
    intro Idx Jdx
    rw [DifferentialGeometry.Analysis.Parabolic.TensorSpectral.tensorChartComponentRaw_def]
    congr 1
    symm
    rw [hTmod_def]
    exact DifferentialGeometry.Analysis.Sobolev.HebeyBlock.triv_eq_toModel_at_chartCenter
      (I := I) r s x (T.toSection x)
  have h_alg :=
    Analysis.Parabolic.TensorSpectral.tensorRSModel_norm_sq_le_sum_projection_sq
      (E := E) r s Tmod
  rw [h_norm_eq]
  refine h_alg.trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl (fun Idx _ => ?_)
  refine Finset.sum_congr rfl (fun Jdx _ => ?_)
  rw [h_raw_eq Idx Jdx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.tensorFiberNorm_sq_le_chartCenterComponents then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.tensorFiberNorm_sq_le_chartCenterComponents"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.tensorFiberNorm_sq_le_chartCenterComponents ``Submission.DifferentialGeometry.Analysis.Sobolev.tensorFiberNorm_sq_le_chartCenterComponents

end DifferentialGeometry.Analysis.Sobolev
