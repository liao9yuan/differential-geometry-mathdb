import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Cutoff
import Submission.DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.HalfLine

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.CompactlySupported _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem HalfLineMetricConvergenceData.exists_inverse_capture_cutoff_at
    (Phi : PointedCGHMaps X P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {t : ℝ} (ht : t ≤ 0)
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I)))
    (z : P.M) (A : Set P.M) (hA : IsCompact A)
    {s epsilon : ℝ} (hs : 0 ≤ s) (hepsilon : 0 < epsilon) :
    ∃ f : C_c(P.M, ℝ),
      (∀ x, f x ∈ _root_.Set.Icc (0 : ℝ) 1) ∧
      _root_.Set.EqOn (⇑f) 1 (A ∪ riemannianClosedBallOf (co.gInf t) z ((1 + epsilon) * s)) ∧
      ∀ᶠ k in _root_.Filter.atTop,
        tsupport f ⊆ (Phi.partialDiffeomorph (co.φ k)).source ∧
        ∀ y ∈ riemannianClosedBallOf ((X.term (phi (co.φ k))).S.base.metric t)
            (Phi.map (co.φ k) z) s,
          y ∈ (Phi.partialDiffeomorph (co.φ k)).target ∧
          (Phi.partialDiffeomorph (co.φ k)).symm y ∈
            (Phi.partialDiffeomorph (co.φ k)).source ∧
          (Phi.partialDiffeomorph (co.φ k))
            ((Phi.partialDiffeomorph (co.φ k)).symm y) = y ∧
          f ((Phi.partialDiffeomorph (co.φ k)).symm y) = 1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Q : PointedRiemannianManifold.{u, uE, uH} (I := I) :=
    { P with metric := co.gInf t }
  let Psi : PointedRiemannianConvergenceMaps (I := I) (X.atTime t) Q (phi ∘ co.φ) :=
    (Phi.compSubseq co.φ co.strictMono).atTimeWithMetric t (co.gInf t)
  have hmetricComplete : RiemannianMetricComplete (I := I) Q.metric :=
    ⟨MetricComplete.complete (I := I) Q hcomplete⟩
  let K := riemannianClosedBallOf Q.metric z ((1 + epsilon) * s + 1)
  have hK : IsCompact K :=
    RiemannianMetricComplete.closedEBall_isCompact hmetricComplete z _
  obtain ⟨C, hcanonical, _hreference⟩ :=
    co.exists_canonicalMetricConvergenceData Phi ht
  have hconv : metricSourceConvergesOn Psi
      (CanonicalMetricCompactness.canonicalSourceData Psi) K 0 := by
    have h := C.converges K hK 0
    rw [funext hcanonical] at h
    exact h
  exact exists_pointed_inverse_capture_cutoff_at Psi z A hA hs
    (by linarith : 1 < 1 + epsilon)
    (by linarith : (1 + epsilon) * s < (1 + epsilon) * s + 1) hK hconv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_inverse_capture_cutoff_at then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_inverse_capture_cutoff_at"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_inverse_capture_cutoff_at ``Submission.DifferentialGeometry.CheegerGromovCompactness.HalfLineMetricConvergenceData.exists_inverse_capture_cutoff_at

end DifferentialGeometry.CheegerGromovCompactness

end
