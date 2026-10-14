import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WitnessTimeRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonTimeRegularity
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.LocalComparisonComposition

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u v uE uH

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {J : ModelWithCorners ℝ E H} [J.Boundaryless]

theorem WindowedModelWitness.exists_composed_comparison
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    (hS : IsSolutionOn S) {delta kappa : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness delta kappa S x t)
    (hreg : ∀ s ∈ _root_.Set.Ioo (-modelDepth delta) 0,
      parabolicTime t (S.scalar t x) s ∈ D.regular)
    (L : PointedFlowData.{v, uE, uH} J ancientTimeInterval)
    (Phi : PartialDiffeomorph J I3 L.M W.model.M ∞)
    (U : TopologicalSpace.Opens L.M) (hU : (U : Set L.M) ⊆ Phi.source)
    (himage : _root_.Set.MapsTo Phi U (riemannianClosedBallOf (W.model.S.base.metric 0)
      W.model.basepoint (modelRadius delta)))
    {A alpha : ℝ} (hA : 0 < A) (hdepth : A < modelDepth delta)
    {order : ℕ} (horder : order ≤ modelOrder delta)
    (halpha : 0 < alpha) (hsmall : alpha ≤ backgroundJetSmallness E order)
    (C : MetricComparisonOn L.S.base.metric W.model.S.base.metric Phi U
      (_root_.Set.Icc (-A) 0) order alpha)
    {K : Set L.M} (hK : IsCompact K) (hKU : K ⊆ U) :
    Nonempty (MetricComparisonOn L.S.base.metric
      (rescaledMetric S t (S.scalar t x) W.scalar_pos)
      (fun y => W.embedding (Phi y)) K (_root_.Set.Icc (-A) 0) order
      (alpha + backgroundJetConstant E order * ((order : ℝ) + 1) * delta)) := by
  have htimes : _root_.Set.Icc (-A) 0 ⊆ _root_.Set.Icc (-modelDepth delta) 0 :=
    _root_.Set.Icc_subset_Icc (neg_le_neg hdepth.le) le_rfl
  have hderiv (b : ℕ) {s : ℝ} (hs : s ∈ _root_.Set.Icc (-A) 0) (y : W.model.M)
      (hy : y ∈ riemannianClosedBallOf (W.model.S.base.metric 0)
        W.model.basepoint (modelRadius delta)) (v : Fin 2 → TangentSpace I3 y) :
      HasDerivWithinAt (fun r => W.comparison.jet b r y v)
        (W.comparison.jet (b + 1) s y v) (_root_.Set.Icc (-A) 0) s :=
    (W.hasDerivWithinAt_comparison_jet hS hreg b
      ⟨lt_of_lt_of_le (neg_lt_neg hdepth) hs.1, hs.2⟩ y hy v).mono htimes
  let c : MetricComparisonOn W.model.S.base.metric
      (rescaledMetric S t (S.scalar t x) W.scalar_pos) W.embedding
      (riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint (modelRadius delta))
      (_root_.Set.Icc (-A) 0) (modelOrder delta) delta := {
    pullback := W.comparison.pullback
    pullback_eq := W.comparison.pullback_eq
    jet := W.comparison.jet
    jet_zero := W.comparison.jet_zero
    jet_succ := fun b s hs y hy v =>
      ((hderiv b hs y hy v).derivWithin (uniqueDiffOn_Icc (neg_neg_of_pos hA) s hs)).symm
    equivalence := fun s hs => W.comparison.equivalence s (htimes hs)
    close := fun a b hab s hs => W.comparison.close a b hab s (htimes hs) }
  have hball : riemannianClosedBallOf (W.model.S.base.metric 0)
      W.model.basepoint (modelRadius delta) ⊆ W.embedding.source :=
    (riemannianClosedBallOf_mono _ _ (le_add_of_nonneg_right zero_le_one)).trans W.buffered_ball
  exact MetricComparisonOn.exists_trans_on_compact Phi W.embedding U hU hball himage
    C c horder W.eps_pos.le halpha hsmall (by
      intro b s hs _hu y hy v
      exact (C.jet_contDiffOn_of_solutions L.S L.isSolution W.model.S W.model.isSolution
        (show -A - 1 < -A by linarith) (show -A - 1 < -A by linarith)
        (neg_neg_of_pos hA) (fun _ hr => hr.2) (fun _ hr => hr.2)
        (fun _ hr => hr.2) (fun _ hr => hr.2) b y hy v s hs).differentiableWithinAt
          (by simp)) (by
      intro b s hs z hz v
      obtain ⟨y, hy, rfl⟩ := hz
      exact (hderiv b hs (Phi y) (himage hy) v).differentiableWithinAt) hK hKU

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.exists_composed_comparison then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.exists_composed_comparison"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.exists_composed_comparison ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.WindowedModelWitness.exists_composed_comparison

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
