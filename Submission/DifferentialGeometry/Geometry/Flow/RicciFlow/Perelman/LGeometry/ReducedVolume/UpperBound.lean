import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.ModelChange
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ReducedVolumeBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  {D : RealTimeInterval}

theorem redVolume_le_one_of_rm
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : ℝ)
    (hg : RiemannianMetricComplete (I := I) (S.base.metric T))
    (x : M)
    (hRm : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := I) (S.base.metric t) z 4 (S.base.rm04 t z) ≤ K)
    {tau : ℝ} (htau : 0 < tau)
    (hslab : _root_.Set.Icc (T - tau) T ⊆ D.regular) :
    redVolume S T x tau ≤ 1 := by
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  let : PseudoMetricSpace M := TopologicalSpace.pseudoMetrizableSpacePseudoMetric M
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
  let J := I.transContinuousLinearEquiv e
  let Φ := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
  let U : SolutionOn (I := J) (M := M) D := S.pullback Φ.symm
  let _ : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) :=
    ⟨by simpa using (NeZero.ne (Module.finrank ℝ E))⟩
  have hU : IsSolutionOn U := hS.pullback S Φ.symm
  have hcomplete : RiemannianMetricComplete (I := J) (U.base.metric T) :=
    RiemannianMetricComplete.pullbackCross (S.base.metric T) Φ.symm hg
  have hRmU : ∀ sigma : ℝ, 0 < sigma → _root_.Set.Icc (T - sigma) T ⊆ D.regular →
      ∃ K : ℝ, ∀ t ∈ _root_.Set.Icc (T - sigma) T, ∀ z : M,
        normSq0S (I := J) (U.base.metric t) z 4 (U.base.rm04 t z) ≤ K := by
    intro sigma hsigma hreg
    obtain ⟨K, hK⟩ := hRm sigma hsigma hreg
    refine ⟨K, fun t ht z => ?_⟩
    change normSq0S (Diffeomorph.pullbackMetricCross (S.base.metric t) Φ.symm) z 4
      (metricRm04At (Diffeomorph.pullbackMetricCross (S.base.metric t) Φ.symm) z) ≤ K
    rw [riemannNormSq_cross]
    exact hK t ht z
  have h := DifferentialGeometry.PDE.RicciFlow.redVolume_le_one_of_rm
    U hU T hcomplete x hRmU tau htau hslab
  change redVolume U T x tau ≤ 1 at h
  rw [redVolume_transContinuousLinearEquiv S e T x tau] at h
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_le_one_of_rm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_le_one_of_rm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_le_one_of_rm ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_le_one_of_rm

end DifferentialGeometry.PDE.RicciFlow.Perelman
