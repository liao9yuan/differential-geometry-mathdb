import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.OpenExhaustion
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.MetricPinchingLimit
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.MetricComparison
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Restriction
import Submission.DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.CurvatureBound
import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instNeZeroNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instNeZeroNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instNeZeroNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry target :: scope.openDecls } }

variable {δ : ℕ → ℝ}

private theorem curvatureOperator_nonnegative_of_neck_metric_limits
    (hcover : ∀ x : NeckCylinder, ∃ n, x ∈ (neckBuffer (δ n) : Set NeckCylinder))
    {D : RealTimeInterval}
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ n)) D)
    {a b : ℝ} (N rho : ℕ → ℕ) (hrho : StrictMono rho)
    (G : ℝ → SmoothRiemannianMetric NeckCylinderModel NeckCylinder)
    (hconv : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ _root_.Set.Icc a b,
        metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
          ((G t).restrictOpen (neckBuffer (δ n)))
          (roundCylinderMetric.restrictOpen (neckBuffer (δ n))) < η)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ i, 0 < Q i) (hQ : _root_.Filter.Tendsto Q _root_.Filter.atTop _root_.Filter.atTop)
    (hpinching : ∀ n, ∀ t ∈ _root_.Set.Icc a b, ∀ᶠ i in _root_.Filter.atTop, ∀ x : neckBuffer (δ n),
      curvatureOperatorLowerBoundAt ((S n i).base.metric t) x
        (metricAlgebraicCurvatureTensorAt ((S n i).base.metric t) x)
        (rescalePinchingFunction (Q (i + N n)) Phi
          (metricScalarAt ((S n i).base.metric t) x))) :
    ∀ t ∈ _root_.Set.Icc a b, ∀ x : NeckCylinder,
      metricAlgebraicCurvatureTensorAt (G t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := NeckCylinderModel) := by
  intro t ht x
  obtain ⟨n, hxn⟩ := hcover x
  let U := neckBuffer (δ n)
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel U.isOpen)
  let j : ℕ → ℕ := fun i => rho i - N n
  have hj : _root_.Filter.Tendsto j _root_.Filter.atTop atTop :=
    (Filter.tendsto_sub_atTop_nat (N n)).comp hrho.tendsto_atTop
  have hjq : _root_.Filter.Tendsto (fun i => Q (j i + N n)) _root_.Filter.atTop atTop :=
    hQ.comp ((_root_.Filter.tendsto_add_atTop_nat (N n)).comp hj)
  have hqj : ∀ i, 0 < Q (j i + N n) := fun i => hQpos _
  have hpinchj : ∀ᶠ i in _root_.Filter.atTop, ∀ y : U, curvatureOperatorLowerBoundAt
      ((S n (j i)).base.metric t) y
      (metricAlgebraicCurvatureTensorAt ((S n (j i)).base.metric t) y)
      (rescalePinchingFunction (Q (j i + N n)) Phi
        (metricScalarAt ((S n (j i)).base.metric t) y)) := by
    exact hj.eventually (hpinching n t ht)
  have hconvU : MetricCInfConvergenceOnCompacts
      (fun i => (S n (j i)).base.metric t)
      ((G t).restrictOpen U)
      (roundCylinderMetric.restrictOpen U) := by
    intro K hK p η hη
    obtain ⟨k, hk⟩ := hconv n K hK p η hη
    exact ⟨k, fun i hi => hk i hi t ht⟩
  have hconeU :=
    FiniteHorn.curvatureOperator_nonnegative_of_metricCInf_admissible_pinching
      (fun i => (S n (j i)).base.metric t)
      ((G t).restrictOpen U) (roundCylinderMetric.restrictOpen U)
      hconvU hPhi (fun i => Q (j i + N n)) hqj hjq hpinchj ⟨x, hxn⟩
  exact (metricAlgebraicCurvatureTensorAt_restrictOpen_mem_curvatureOperatorNonnegativeCone_iff
    (G t) U ⟨x, hxn⟩).mp hconeU

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.curvatureOperator_nonnegative_of_neck_metric_limits
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.curvatureOperator_nonnegative_of_neck_metric_limits target :: scope.openDecls } }

private theorem ricci_nonnegative_and_complete_of_terminal_roundCylinder
    {a b : ℝ} (hab : a < b)
    (G : ℝ → SmoothRiemannianMetric NeckCylinderModel NeckCylinder)
    (hGb : G b = roundCylinderMetric)
    (hGsol : IsSolutionOn ({ base.metric := G } : SolutionOn (I := NeckCylinderModel)
      (M := NeckCylinder) (RealTimeInterval.closed a b hab.le)))
    (hnonneg : ∀ t ∈ _root_.Set.Icc a b, ∀ x : NeckCylinder,
      metricAlgebraicCurvatureTensorAt (G t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := NeckCylinderModel)) :
    (∀ t ∈ _root_.Set.Icc a b, ∀ x : NeckCylinder, ∀ v : TangentSpace NeckCylinderModel x,
      0 ≤ ricciTensor (G t) x v v) ∧
    (∀ t ∈ _root_.Set.Icc a b, RiemannianMetricComplete (G t)) := by
  have hcompleteR : RiemannianMetricComplete roundCylinderMetric := by
    rw [roundCylinderMetric_eq_geometry]
    simpa only [PDE.RicciFlow.shrinkingCylinderMetric_zero] using
      (PDE.RicciFlow.shrinkingCylinderMetric_complete (E := ThreeSpace) 0)
  have hRic : ∀ t ∈ _root_.Set.Icc a b, ∀ x : NeckCylinder,
      ∀ v : TangentSpace NeckCylinderModel x, 0 ≤ ricciTensor (G t) x v v := by
    intro t ht x v
    have h := metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      (G t) x (hnonneg t ht x) v
    rwa [metricRicciAt_apply_eq_ricciTensor] at h
  let L : SolutionOn (I := NeckCylinderModel) (M := NeckCylinder)
      (RealTimeInterval.closed a b hab.le) := { base.metric := G }
  have hRicAt : ∀ s ∈ _root_.Set.Ioo a b, ∀ x : NeckCylinder,
      ∀ v : TangentSpace NeckCylinderModel x, 0 ≤ L.ricciAt s x (vec2 v v) := by
    intro s hs x v
    change 0 ≤ metricRicciAt (G s) x (vec2 v v)
    rw [metricRicciAt_apply_eq_ricciTensor]
    exact hRic s ⟨hs.1.le, hs.2.le⟩ x v
  have hcompleteb : RiemannianMetricComplete (L.base.metric b) := by
    change RiemannianMetricComplete (G b)
    rwa [hGb]
  have hcomplete : ∀ t ∈ _root_.Set.Icc a b, RiemannianMetricComplete (G t) := by
    intro t ht
    exact complete_at_earlier_time_of_ricci_nonnegative L hGsol
      (Subset.rfl : _root_.Set.Icc a b ⊆ (RealTimeInterval.closed a b hab.le).carrier)
      (Subset.rfl : _root_.Set.Ioo a b ⊆ (RealTimeInterval.closed a b hab.le).regular)
      hRicAt hcompleteb ht
  exact ⟨hRic, hcomplete⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ricci_nonnegative_and_complete_of_terminal_roundCylinder
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ricci_nonnegative_and_complete_of_terminal_roundCylinder target :: scope.openDecls } }

theorem exists_global_complete_nonnegative_neck_limit
    (hδ : ∀ n, 0 < δ n) (hδlim : _root_.Filter.Tendsto δ _root_.Filter.atTop (𝓝 0))
    {D : RealTimeInterval}
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ n)) D)
    (hS : ∀ n i, IsSolutionOn (S n i))
    {a b : ℝ} (hab : a < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ico a b ⊆ D.regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric b)
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n))))
    (hcurv : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in _root_.Filter.atTop,
        ∀ t ∈ _root_.Set.Icc a b, ∀ x ∈ K, curvDerivNorm q ((S n i).base.metric t) x ≤ C)
    (N : ℕ → ℕ)
    (hcompat : ∀ n m t, t ∈ _root_.Set.Icc a b →
      (fun i => ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ n))) =ᶠ[_root_.Filter.atTop]
      (fun i => ((S m (i - N m)).base.metric t).restrictOpenOfSubset
        (inf_le_right : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ m))))
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ i, 0 < Q i) (hQ : _root_.Filter.Tendsto Q _root_.Filter.atTop _root_.Filter.atTop)
    (hpinching : ∀ n, ∀ t ∈ _root_.Set.Icc a b, ∀ᶠ i in _root_.Filter.atTop, ∀ x : neckBuffer (δ n),
      curvatureOperatorLowerBoundAt ((S n i).base.metric t) x
        (metricAlgebraicCurvatureTensorAt ((S n i).base.metric t) x)
        (rescalePinchingFunction (Q (i + N n)) Phi
          (metricScalarAt ((S n i).base.metric t) x))) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∃ G : ℝ → SmoothRiemannianMetric NeckCylinderModel NeckCylinder,
        G b = roundCylinderMetric ∧
        IsSolutionOn ({ base.metric := G } : SolutionOn (I := NeckCylinderModel)
          (M := NeckCylinder) (RealTimeInterval.closed a b hab.le)) ∧
        (∀ t ∈ _root_.Set.Icc a b, ∀ x : NeckCylinder,
          metricAlgebraicCurvatureTensorAt (G t) x ∈
            algebraicCurvatureOperatorNonnegativeCone (I := NeckCylinderModel)) ∧
        (∀ t ∈ _root_.Set.Icc a b, ∀ x : NeckCylinder, ∀ v : TangentSpace NeckCylinderModel x,
          0 ≤ ricciTensor (G t) x v v) ∧
        (∀ t ∈ _root_.Set.Icc a b, RiemannianMetricComplete (G t)) ∧
        ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
          ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ _root_.Set.Icc a b,
            metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
              ((G t).restrictOpen (neckBuffer (δ n)))
              (roundCylinderMetric.restrictOpen (neckBuffer (δ n))) < η := by
  have hcover : ∀ x : NeckCylinder, ∃ n, x ∈ (neckBuffer (δ n) : Set NeckCylinder) := by
    intro x
    apply mem_iUnion.mp
    rw [iUnion_neckBuffer_eq_univ_of_tendsto_zero hδ hδlim]
    exact _root_.Set.mem_univ x
  obtain ⟨rho, hrho, G, hGb, hGsol, hconv⟩ :=
    exists_global_solution_subsequence_of_terminal_convergence_on_open_cover
      (fun n => neckBuffer (δ n)) hcover S hS roundCylinderMetric hab hslab hreg
      hterminal hcurv N hcompat
  have hnonneg := curvatureOperator_nonnegative_of_neck_metric_limits hcover S N rho hrho G
    hconv hPhi Q hQpos hQ hpinching
  obtain ⟨hRic, hcomplete⟩ :=
    ricci_nonnegative_and_complete_of_terminal_roundCylinder hab G hGb hGsol hnonneg
  exact ⟨rho, hrho, G, hGb, hGsol, hnonneg, hRic, hcomplete, hconv⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_global_complete_nonnegative_neck_limit then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_global_complete_nonnegative_neck_limit"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_global_complete_nonnegative_neck_limit ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_global_complete_nonnegative_neck_limit

theorem normSq_rm_le_of_neck_metric_limits
    {δ : ℕ → ℝ}
    (hcover : ∀ x : NeckCylinder, ∃ n, x ∈ (neckBuffer (δ n) : Set NeckCylinder))
    {D : RealTimeInterval}
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ n)) D)
    {a b : ℝ} (N rho : ℕ → ℕ) (hrho : StrictMono rho)
    (G : ℝ → SmoothRiemannianMetric NeckCylinderModel NeckCylinder)
    (hconv : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
      ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ _root_.Set.Icc a b,
        metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
          ((G t).restrictOpen (neckBuffer (δ n)))
          (roundCylinderMetric.restrictOpen (neckBuffer (δ n))) < η)
    (hnonneg : ∀ t ∈ _root_.Set.Icc a b, ∀ x : NeckCylinder,
      metricAlgebraicCurvatureTensorAt (G t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := NeckCylinderModel))
    {C : ℝ}
    (hbound : ∀ n, ∀ t ∈ _root_.Set.Icc a b, ∀ x : neckBuffer (δ n), ∀ᶠ i in _root_.Filter.atTop,
      normSq0S ((S n i).base.metric t) x 4 (metricRm04At ((S n i).base.metric t) x) ≤ C) :
    ∀ t ∈ _root_.Set.Icc a b, ∀ x : NeckCylinder,
      normSq0S (G t) x 4 (metricRm04At (G t) x) ≤ 100 ^ 2 * (9 * Real.sqrt C) ^ 2 := by
  intro t ht x
  obtain ⟨n, hxn⟩ := hcover x
  let U := neckBuffer (δ n)
  let _ : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel U.isOpen)
  let y : U := ⟨x, hxn⟩
  have hj : _root_.Filter.Tendsto (fun i => rho i - N n) _root_.Filter.atTop atTop :=
    (_root_.Filter.tendsto_sub_atTop_nat (N n)).comp hrho.tendsto_atTop
  have hconvU : MetricCInfConvergenceOnCompacts
      (fun i => (S n (rho i - N n)).base.metric t)
      ((G t).restrictOpen U) (roundCylinderMetric.restrictOpen U) := by
    intro K hK p η hη
    obtain ⟨k, hk⟩ := hconv n K hK p η hη
    exact ⟨k, fun i hi => hk i hi t ht⟩
  have hconeU :=
    (metricAlgebraicCurvatureTensorAt_restrictOpen_mem_curvatureOperatorNonnegativeCone_iff
      (G t) U y).mpr (hnonneg t ht x)
  have hR := normSq_rm_le_of_metricCP_of_curvatureOperator_nonnegative
    (fun i => (S n (rho i - N n)).base.metric t)
    ((G t).restrictOpen U) (roundCylinderMetric.restrictOpen U) y
    (hconvU {y} isCompact_singleton 2)
    (by simp [Module.finrank_prod]) hconeU
    (hj.eventually (hbound n t ht y))
  have hrm : metricRm04At ((G t).restrictOpen U) y = metricRm04At (G t) x := by
    ext slots
    exact curvCovDeriv_restrictOpen (G t) U 0 y slots
  rw [normSq0S_restrictOpen_apply, hrm] at hR
  exact hR

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.normSq_rm_le_of_neck_metric_limits then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.normSq_rm_le_of_neck_metric_limits"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.normSq_rm_le_of_neck_metric_limits ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.normSq_rm_le_of_neck_metric_limits


theorem exists_global_complete_nonnegative_neck_limit_of_curvature_bound
    (hδ : ∀ n, 0 < δ n) (hδlim : _root_.Filter.Tendsto δ _root_.Filter.atTop (𝓝 0))
    {D : RealTimeInterval}
    (S : ∀ n : ℕ, ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer (δ n)) D)
    (hS : ∀ n i, IsSolutionOn (S n i))
    {a b : ℝ} (hab : a < b)
    (hslab : _root_.Set.Icc a b ⊆ D.carrier) (hreg : _root_.Set.Ico a b ⊆ D.regular)
    (hterminal : ∀ n, MetricCInfConvergenceOnCompacts
      (fun i => (S n i).base.metric b)
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n)))
      (roundCylinderMetric.restrictOpen (neckBuffer (δ n))))
    (hcurv : ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ q : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ i in _root_.Filter.atTop,
        ∀ t ∈ _root_.Set.Icc a b, ∀ x ∈ K, curvDerivNorm q ((S n i).base.metric t) x ≤ C)
    (N : ℕ → ℕ)
    (hcompat : ∀ n m t, t ∈ _root_.Set.Icc a b →
      (fun i => ((S n (i - N n)).base.metric t).restrictOpenOfSubset
        (inf_le_left : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ n))) =ᶠ[_root_.Filter.atTop]
      (fun i => ((S m (i - N m)).base.metric t).restrictOpenOfSubset
        (inf_le_right : neckBuffer (δ n) ⊓ neckBuffer (δ m) ≤ neckBuffer (δ m))))
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (Q : ℕ → ℝ) (hQpos : ∀ i, 0 < Q i) (hQ : _root_.Filter.Tendsto Q _root_.Filter.atTop _root_.Filter.atTop)
    (hpinching : ∀ n, ∀ t ∈ _root_.Set.Icc a b, ∀ᶠ i in _root_.Filter.atTop, ∀ x : neckBuffer (δ n),
      curvatureOperatorLowerBoundAt ((S n i).base.metric t) x
        (metricAlgebraicCurvatureTensorAt ((S n i).base.metric t) x)
        (rescalePinchingFunction (Q (i + N n)) Phi
          (metricScalarAt ((S n i).base.metric t) x)))
    {C : ℝ}
    (hbound : ∀ n, ∀ t ∈ _root_.Set.Icc a b, ∀ x : neckBuffer (δ n), ∀ᶠ i in _root_.Filter.atTop,
      normSq0S ((S n i).base.metric t) x 4 (metricRm04At ((S n i).base.metric t) x) ≤ C) :
    ∃ rho : ℕ → ℕ, StrictMono rho ∧
      ∃ G : ℝ → SmoothRiemannianMetric NeckCylinderModel NeckCylinder,
        G b = roundCylinderMetric ∧
        IsSolutionOn ({ base.metric := G } : SolutionOn (I := NeckCylinderModel)
          (M := NeckCylinder) (RealTimeInterval.closed a b hab.le)) ∧
        (∀ t ∈ _root_.Set.Icc a b, ∀ x : NeckCylinder,
          metricAlgebraicCurvatureTensorAt (G t) x ∈
            algebraicCurvatureOperatorNonnegativeCone (I := NeckCylinderModel)) ∧
        (∀ t ∈ _root_.Set.Icc a b, ∀ x : NeckCylinder, ∀ v : TangentSpace NeckCylinderModel x,
          0 ≤ ricciTensor (G t) x v v) ∧
        (∀ t ∈ _root_.Set.Icc a b, RiemannianMetricComplete (G t)) ∧
        (∀ t ∈ _root_.Set.Icc a b, ∀ x : NeckCylinder,
          normSq0S (G t) x 4 (metricRm04At (G t) x) ≤ 100 ^ 2 * (9 * Real.sqrt C) ^ 2) ∧
        ∀ n, ∀ K : Set (neckBuffer (δ n)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
          ∃ j : ℕ, ∀ i ≥ j, ∀ t ∈ _root_.Set.Icc a b,
            metricDerivNormSupOn K p ((S n (rho i - N n)).base.metric t)
              ((G t).restrictOpen (neckBuffer (δ n)))
              (roundCylinderMetric.restrictOpen (neckBuffer (δ n))) < η := by
  obtain ⟨rho, hrho, G, hGb, hGsol, hnonneg, hRic, hcomplete, hconv⟩ :=
    exists_global_complete_nonnegative_neck_limit hδ hδlim S hS hab hslab hreg
      hterminal hcurv N hcompat hPhi Q hQpos hQ hpinching
  have hcover : ∀ x : NeckCylinder, ∃ n, x ∈ (neckBuffer (δ n) : Set NeckCylinder) := by
    intro x
    apply mem_iUnion.mp
    rw [iUnion_neckBuffer_eq_univ_of_tendsto_zero hδ hδlim]
    exact _root_.Set.mem_univ x
  refine ⟨rho, hrho, G, hGb, hGsol, hnonneg, hRic, hcomplete, ?_, hconv⟩
  exact normSq_rm_le_of_neck_metric_limits hcover S N rho hrho G hconv hnonneg hbound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_global_complete_nonnegative_neck_limit_of_curvature_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_global_complete_nonnegative_neck_limit_of_curvature_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_global_complete_nonnegative_neck_limit_of_curvature_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_global_complete_nonnegative_neck_limit_of_curvature_bound


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
