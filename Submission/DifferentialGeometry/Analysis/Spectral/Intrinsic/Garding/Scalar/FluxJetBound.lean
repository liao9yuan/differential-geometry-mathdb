import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Scalar.Nonautonomous.TameBound
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.MetricLaplacianDifference.TimeDependence
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricPerturbation.Family.Difference
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.ConnectionDifference.MetricComparisonEndomorphismJetBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Parametric.JetBounds
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Metric.CometricFamilyRegularity
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.MetricPerturbationPath.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.Variation.ConnectionDifference
import Submission.DifferentialGeometry.Analysis.Parabolic.RicciLinearization.ResidualCoefficient.Decomposition
import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.MetricRealization.Perturbation.GramDifference
import Submission.DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair
import Submission.DifferentialGeometry.Geometry.Metric.RiemannianMetricTensor

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Tensor.RSTensor
open _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection

noncomputable section
set_option backward.isDefEq.respectTransparency false

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.InnerProductSpace

namespace DifferentialGeometry.Analysis.Spectral

open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.TensorHilbert
open _root_.Submission.DifferentialGeometry.PDE.DeTurck.RicciLinearization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.MetricRealization
open _root_.Submission.DifferentialGeometry.Analysis.Spectral.DeTurck

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1 : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.instCompleteSpace_differentialGeometry_1 target :: scope.openDecls } }

private local instance scalarFluxTensorRSModelNormedAddCommGroup (r s : ℕ) :
    NormedAddCommGroup (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedAddCommGroup r s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.scalarFluxTensorRSModelNormedAddCommGroup
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.scalarFluxTensorRSModelNormedAddCommGroup target :: scope.openDecls } }

private local instance scalarFluxTensorRSModelNormedSpace (r s : ℕ) :
    NormedSpace ℝ (TensorRSModel r s ℝ E) :=
  Tensor0SBundle.tensorRSModelNormedSpace r s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.scalarFluxTensorRSModelNormedSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.scalarFluxTensorRSModelNormedSpace target :: scope.openDecls } }

private local instance scalarFluxTensorRSTotalSpaceTopology (r s : ℕ) :
    TopologicalSpace
      (_root_.Bundle.TotalSpace (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x)) :=
  Tensor0SBundle.tensorRSBundleTopology r s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.scalarFluxTensorRSTotalSpaceTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.scalarFluxTensorRSTotalSpaceTopology target :: scope.openDecls } }

private local instance scalarFluxTensorRSFiberBundle (r s : ℕ) :
    FiberBundle (TensorRSModel r s ℝ E) (fun x : M => TensorRSSpace r s I x) :=
  Tensor0SBundle.tensorRSBundleFiber r s

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.scalarFluxTensorRSFiberBundle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.scalarFluxTensorRSFiberBundle target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [SigmaCompactSpace M] in
theorem metricDifference_bilin (q h : SmoothRiemannianMetric I M)
    (x : M) (v w : TangentSpace I x) :
    ccTensorBilinSymm (I := I) q
        (metricDifferenceCcTensor (I := I) (M := M) q h) x v w =
      h.inner x v w - q.inner x v w :=
  metricDifference_symVal (I := I) (M := M) q h x v w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.metricDifference_bilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.metricDifference_bilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.metricDifference_bilin ``Submission.DifferentialGeometry.Analysis.Spectral.metricDifference_bilin

private lemma grid_mono {a b : ℕ → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hab : ∀ j, a j ≤ b j) (i : ℕ) :
    DifferentialGeometry.Combinatorics.antidiagonalTupleGrid a i ≤
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid b i := by
  classical
  rw [DifferentialGeometry.Combinatorics.antidiagonalTupleGrid,
    DifferentialGeometry.Combinatorics.antidiagonalTupleGrid]
  refine Finset.sum_le_sum (fun n _ => Finset.sum_le_sum (fun e _ => ?_))
  exact Finset.prod_le_prod (fun m _ => ha (e m)) (fun m _ => hab (e m))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.grid_mono
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.grid_mono target :: scope.openDecls } }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M] in
private theorem joint0S_sub {d : ℕ} {S : Set ℝ}
    (A B : ∀ p : M × ℝ, Tensor0SSpace d I p.1)
    (hA : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p))
      ((Set.univ : Set M) ×ˢ S))
    (hB : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (B p))
      ((Set.univ : Set M) ×ˢ S)) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel d ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel d ℝ E)
        (E := fun z : M => Tensor0SSpace d I z) p.1 (A p - B p))
      ((Set.univ : Set M) ×ˢ S) := by
  let := tensor0SBundleTopology (𝕜 := ℝ) (E := E) (H := H)
    (I := I) (M := M) d
  intro p₀ hp₀
  rw [Bundle.contMDiffWithinAt_totalSpace]
  refine ⟨contMDiffWithinAt_fst, ?_⟩
  set x₀ := p₀.1 with hx₀
  set e := _root_.FiberBundle.trivializationAt (Tensor0SModel d ℝ E)
    (fun z : M => Tensor0SSpace d I z) x₀ with he
  have hA' := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hA p₀ hp₀)
  have hB' := (Bundle.contMDiffWithinAt_totalSpace
    (F := Tensor0SModel d ℝ E)
    (E := fun z : M => Tensor0SSpace d I z)).mp (hB p₀ hp₀)
  refine (hA'.2.sub hB'.2).congr_of_eventuallyEq ?_ ?_
  · have hbase : ∀ᶠ p : M × ℝ in nhdsWithin p₀
        ((Set.univ : Set M) ×ˢ S), p.1 ∈ e.baseSet :=
      (continuousWithinAt_fst
        (s := (Set.univ : Set M) ×ˢ S) (p := p₀))
        (e.open_baseSet.mem_nhds (by
          rw [he]
          exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀))
    filter_upwards [hbase] with p hp
    exact ((e.linear ℝ hp).map_sub (A p) (B p)).symm
  · exact ((e.linear ℝ (by
      rw [he, ← hx₀]
      exact _root_.FiberBundle.mem_baseSet_trivializationAt _ _ x₀)).map_sub
        (A p₀) (B p₀)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.joint0S_sub
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.joint0S_sub target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricDifference_small
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (T : ℝ), ∀ i : ℕ, i ≤ p → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) (g_fam (T : ℝ)) 0 (2 + i) x
        ((iteratedCovGrad (I := I) (g_fam (T : ℝ)) 0 2 i
          (metricDifferenceCcTensor (I := I) (M := M)
            (g_fam (T : ℝ)) (g_fam t))).toSection x) < ε := by
  let q : SmoothRiemannianMetric I M := g_fam (T : ℝ)
  let P : ℝ → SmoothCcTensor q 0 2 := fun t =>
    metricDifferenceCcTensor (I := I) (M := M) q (g_fam t)
  have hPzero : P (T : ℝ) = 0 := by
    simp only [P, q, metricDifferenceCcTensor_self]
  have hPjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun z : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun y : M => TensorRSSpace 0 2 I y) z.1
        ((P z.2).toSection z.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    simpa only [P, q] using metricDifference_joint (I := I) (M := M) g_fam hG q
  simpa only [P, q] using
    joint_jet_small (I := I) (M := M) q 0 2 p P
      (D.regular_isOpen.mem_nhds T.2) hPzero hPjoint hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.metricDifference_small then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.metricDifference_small"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.metricDifference_small ``Submission.DifferentialGeometry.Analysis.Spectral.metricDifference_small

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem scalarTrace_joint
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (q : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 2 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 2 0 ℝ E)
        (E := fun x : M => TensorRSSpace 2 0 I x) p.1
        ((scalarTraceCoeff (I := I) (M := M) q (g_fam p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := Tensor0SModel 2 ℝ E) (V₁ := fun x : M => Tensor0SSpace 2 I x)
    (F₂ := Tensor0SModel 0 ℝ E) (V₂ := fun x : M => Tensor0SSpace 0 I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace 2 I p.1 →L[ℝ] Tensor0SSpace 0 I p.1 from
        (scalarTraceCoeff (I := I) (M := M) q (g_fam p.2)).toSection p.1))
    (S := D.regular)
  intro W
  have hW : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 2 ℝ E)
        (E := fun x : M => Tensor0SSpace 2 I x) p.1 (W p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    exact W.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hmove := MetricFamilySmoothOn.cometricDoubleTraceFib_jointContMDiffOn
    (I := I) 0 g_fam hG
    (fun p : M × ℝ => W p.1) hW
  have hfixedOp : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 2 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 2 0 ℝ E)
        (E := fun x : M => TensorRSSpace 2 0 I x) p.1
        (cometricDoubleTraceFib (I := I) q 0 p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    exact (cometricDoubleTraceFib_contMDiff (I := I) q 0).comp_contMDiffOn
      contMDiffOn_fst
  have hfixed := ContMDiffOn.clm_bundle_apply (b := Prod.fst) hfixedOp hW
  have hsub := joint0S_sub (I := I) (M := M) (d := 0)
    (fun p : M × ℝ =>
      cometricDoubleTraceFib (I := I) (g_fam p.2) 0 p.1 (W p.1))
    (fun p : M × ℝ => cometricDoubleTraceFib (I := I) q 0 p.1 (W p.1))
    hmove hfixed
  refine hsub.congr (fun p _ => ?_)
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarTrace_joint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarTrace_joint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarTrace_joint ``Submission.DifferentialGeometry.Analysis.Spectral.scalarTrace_joint

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connTrace_joint
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (q : SmoothRiemannianMetric I M) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 1 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 1 0 ℝ E)
        (E := fun x : M => TensorRSSpace 1 0 I x) p.1
        ((connTraceCoeff (I := I) (M := M) q (g_fam p.2)).toSection p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
  apply contMDiffOn_clm_section_of_apply (I := I) (M := M)
    (F₁ := Tensor0SModel 1 ℝ E) (V₁ := fun x : M => Tensor0SSpace 1 I x)
    (F₂ := Tensor0SModel 0 ℝ E) (V₂ := fun x : M => Tensor0SSpace 0 I x)
    (φ := fun p : M × ℝ =>
      (show Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SSpace 0 I p.1 from
        (connTraceCoeff (I := I) (M := M) q (g_fam p.2)).toSection p.1))
    (S := D.regular)
  intro W
  have hW : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, Tensor0SModel 1 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (Tensor0SModel 1 ℝ E)
        (E := fun x : M => Tensor0SSpace 1 I x) p.1 (W p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    exact W.contMDiff.comp_contMDiffOn contMDiffOn_fst
  have hconn := ContMDiffOn.clm_bundle_apply (b := Prod.fst)
    (connectionDifference_joint (I := I) g_fam hG q) hW
  have htrace := MetricFamilySmoothOn.cometricDoubleTraceFib_jointContMDiffOn
    (I := I) 0 g_fam hG
    (fun p : M × ℝ =>
      (show Tensor0SSpace 1 I p.1 →L[ℝ] Tensor0SSpace 2 I p.1 from
        connectionDifferenceFib (I := I) (g_fam p.2) q p.1) (W p.1)) hconn
  refine htrace.congr (fun p _ => ?_)
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.connTrace_joint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.connTrace_joint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.connTrace_joint ``Submission.DifferentialGeometry.Analysis.Spectral.connTrace_joint

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem scalarTrace_rev
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (q : SmoothRiemannianMetric I M) (T : ℝ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 2 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 2 0 ℝ E)
        (E := fun x : M => TensorRSSpace 2 0 I x) p.1
        ((scalarTraceCoeff (I := I) (M := M) q
          (g_fam (T - p.2))).toSection p.1))
      ((Set.univ : Set M) ×ˢ {s : ℝ | T - s ∈ D.regular}) := by
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : M × ℝ => (p.1, T - p.2))
      ((Set.univ : Set M) ×ˢ {s : ℝ | T - s ∈ D.regular}) := by
    exact ContMDiffOn.prodMk contMDiffOn_fst
      (ContMDiffOn.sub contMDiffOn_const contMDiffOn_snd)
  with_unfolding_all
    exact (scalarTrace_joint (I := I) (M := M) g_fam hG q).comp hmove
      (fun p hp => ⟨Set.mem_univ p.1, hp.2⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarTrace_rev then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarTrace_rev"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarTrace_rev ``Submission.DifferentialGeometry.Analysis.Spectral.scalarTrace_rev

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connTrace_rev
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (q : SmoothRiemannianMetric I M) (T : ℝ) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 1 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 1 0 ℝ E)
        (E := fun x : M => TensorRSSpace 1 0 I x) p.1
        ((connTraceCoeff (I := I) (M := M) q
          (g_fam (T - p.2))).toSection p.1))
      ((Set.univ : Set M) ×ˢ {s : ℝ | T - s ∈ D.regular}) := by
  have hmove : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, ℝ)) ∞
      (fun p : M × ℝ => (p.1, T - p.2))
      ((Set.univ : Set M) ×ˢ {s : ℝ | T - s ∈ D.regular}) := by
    exact ContMDiffOn.prodMk contMDiffOn_fst
      (ContMDiffOn.sub contMDiffOn_const contMDiffOn_snd)
  with_unfolding_all
    exact (connTrace_joint (I := I) (M := M) g_fam hG q).comp hmove
      (fun p hp => ⟨Set.mem_univ p.1, hp.2⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.connTrace_rev then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.connTrace_rev"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.connTrace_rev ``Submission.DifferentialGeometry.Analysis.Spectral.connTrace_rev

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem scalarTrace_rev_on
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (q : SmoothRiemannianMetric I M) (T : ℝ) {S : Set ℝ}
    (hS : S ⊆ {s : ℝ | T - s ∈ D.regular}) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 2 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 2 0 ℝ E)
        (E := fun x : M => TensorRSSpace 2 0 I x) p.1
        ((scalarTraceCoeff (I := I) (M := M) q
          (g_fam (T - p.2))).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) :=
  (scalarTrace_rev (I := I) (M := M) g_fam hG q T).mono
    (Set.prod_mono (Set.Subset.rfl) hS)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarTrace_rev_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarTrace_rev_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarTrace_rev_on ``Submission.DifferentialGeometry.Analysis.Spectral.scalarTrace_rev_on

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem connTrace_rev_on
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (q : SmoothRiemannianMetric I M) (T : ℝ) {S : Set ℝ}
    (hS : S ⊆ {s : ℝ | T - s ∈ D.regular}) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 1 0 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 1 0 ℝ E)
        (E := fun x : M => TensorRSSpace 1 0 I x) p.1
        ((connTraceCoeff (I := I) (M := M) q
          (g_fam (T - p.2))).toSection p.1))
      ((Set.univ : Set M) ×ˢ S) :=
  (connTrace_rev (I := I) (M := M) g_fam hG q T).mono
    (Set.prod_mono (Set.Subset.rfl) hS)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.connTrace_rev_on then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.connTrace_rev_on"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.connTrace_rev_on ``Submission.DifferentialGeometry.Analysis.Spectral.connTrace_rev_on

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem scalarTrace_small
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (T : ℝ), ∀ i : ℕ, i ≤ p → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) (g_fam (T : ℝ)) 2 (0 + i) x
        ((iteratedCovGrad (I := I) (g_fam (T : ℝ)) 2 0 i
          (scalarTraceCoeff (I := I) (M := M) (g_fam (T : ℝ))
            (g_fam t))).toSection x) < ε := by
  let q : SmoothRiemannianMetric I M := g_fam (T : ℝ)
  let P : ℝ → SmoothCcTensor q 2 0 := fun t =>
    scalarTraceCoeff (I := I) (M := M) q (g_fam t)
  have hPzero : P (T : ℝ) = 0 := by
    simp only [P, q, scalarTraceCoeff, traceCast_self, sub_self]
  have hPjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 2 0 ℝ E)) ∞
      (fun z : M × ℝ => TotalSpace.mk' (TensorRSModel 2 0 ℝ E)
        (E := fun y : M => TensorRSSpace 2 0 I y) z.1
        ((P z.2).toSection z.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    simpa only [P, q] using scalarTrace_joint (I := I) (M := M) g_fam hG q
  simpa only [P, q, Nat.zero_add] using
    joint_jet_small (I := I) (M := M) q 2 0 p P
      (D.regular_isOpen.mem_nhds T.2) hPzero hPjoint hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarTrace_small then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarTrace_small"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarTrace_small ``Submission.DifferentialGeometry.Analysis.Spectral.scalarTrace_small

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
private theorem connFib_self (q : SmoothRiemannianMetric I M) (x : M) :
    connectionDifferenceFib (I := I) q q x = 0 := by
  apply ContinuousLinearMap.ext
  intro om
  apply ContinuousMultilinearMap.ext
  intro YZ
  with_unfolding_all
    change ((show Tensor0SSpace 1 I x →L[ℝ] Tensor0SSpace 2 I x from
      connectionDifferenceFib (I := I) q q x) om) YZ = 0
  rw [connectionDifferenceFib_apply_eval, PDE.DeTurck.connectionDifference_self]
  change om (0 : Fin 1 → TangentSpace I x) = 0
  exact ContinuousMultilinearMap.map_zero om

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Spectral.connFib_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Spectral.connFib_self target :: scope.openDecls } }

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem connTrace_small
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (T : ℝ), ∀ i : ℕ, i ≤ p → ∀ x : M,
      riemannianFiberNormSq (I := I) (M := M) (g_fam (T : ℝ)) 1 (0 + i) x
        ((iteratedCovGrad (I := I) (g_fam (T : ℝ)) 1 0 i
          (connTraceCoeff (I := I) (M := M) (g_fam (T : ℝ))
            (g_fam t))).toSection x) < ε := by
  let q : SmoothRiemannianMetric I M := g_fam (T : ℝ)
  let P : ℝ → SmoothCcTensor q 1 0 := fun t =>
    connTraceCoeff (I := I) (M := M) q (g_fam t)
  have hPzero : P (T : ℝ) = 0 := by
    apply SmoothCcTensor.ext
    apply ContMDiffSection.ext
    intro x
    dsimp only [P, q]
    rw [connTraceCoeff, operatorFieldComposition_toSection, traceCast,
      SmoothCcTensor.retag_toSection, cometricDoubleTraceField_toSection,
      connectionDifferenceSection_toSection, connFib_self (I := I) (M := M),
      ContinuousLinearMap.comp_zero, SmoothCcTensor.toSection_zero]
    rfl
  have hPjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 1 0 ℝ E)) ∞
      (fun z : M × ℝ => TotalSpace.mk' (TensorRSModel 1 0 ℝ E)
        (E := fun y : M => TensorRSSpace 1 0 I y) z.1
        ((P z.2).toSection z.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    simpa only [P, q] using connTrace_joint (I := I) (M := M) g_fam hG q
  simpa only [P, q, Nat.zero_add] using
    joint_jet_small (I := I) (M := M) q 1 0 p P
      (D.regular_isOpen.mem_nhds T.2) hPzero hPjoint hε

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.connTrace_small then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.connTrace_small"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.connTrace_small ``Submission.DifferentialGeometry.Analysis.Spectral.connTrace_small

omit [NeZero (Module.finrank ℝ E)] [BoundarylessManifold I M] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem scalarFlux_eq_slot (q h : SmoothRiemannianMetric I M) :
    scalarFluxCoeff (I := I) (M := M) q h =
      endoSlotZeroCcTensor (I := I) (M := M) q 0
      (metricComparisonDifferenceEndomorphismField (I := I) (M := M) q h) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply tensorRSSpace_ext 1 1 x
  intro om
  apply cotangentToDualLinear_injective (I := I) (x := x)
  apply LinearMap.ext
  intro w
  rw [cotangentToDualLinear_apply, cotangentToDualLinear_apply]
  rw [scalarFlux_eval (I := I) (M := M), slotInsertEndoCc_toSection,
    cotangent_slot_apply (I := I) (M := M)]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarFlux_eq_slot then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarFlux_eq_slot"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarFlux_eq_slot ``Submission.DifferentialGeometry.Analysis.Spectral.scalarFlux_eq_slot

omit [SigmaCompactSpace M] in
theorem scalarFlux_jet_grid
    (q : SmoothRiemannianMetric I M) {δ₀ : ℝ} (hδ₀ : δ₀ < 1) :
    ∃ C : ℕ → ℝ, (∀ i, 0 ≤ C i) ∧
      ∀ (h : SmoothRiemannianMetric I M) (T : SmoothCcTensor q 0 2)
        (_htie : ∀ y v w, h.inner y v w =
          q.inner y v w + ccTensorBilinSymm (I := I) q T y v w)
        {δ : ℝ} (_hδ_le : δ ≤ δ₀) (_hδ0 : 0 ≤ δ)
        (_hbound : metricCauchySchwarzBound (I := I) q
          (ccTensorBilinSymm (I := I) q T) δ)
        (i : ℕ) (x : M),
        riemannianFiberNormSq (I := I) (M := M) q 1 (1 + i) x
            ((iteratedCovGrad (I := I) q 1 1 i
              (scalarFluxCoeff (I := I) (M := M) q h)).toSection x) ≤
          C i * DifferentialGeometry.Combinatorics.antidiagonalTupleGrid
            (fun j => riemannianFiberNormSq (I := I) (M := M) q 0 (2 + j) x
              ((iteratedCovGrad (I := I) q 0 2 j T).toSection x)) i := by
  obtain ⟨C, hC, hjet⟩ :=
    riemannianFiberNormSq_iteratedCovGrad_slotInsertEndoCc_zero_metricComparisonDifferenceEndomorphism_diagGrid_le
      (I := I) (M := M) q hδ₀
  refine ⟨C, hC, ?_⟩
  intro h T htie δ hδ_le hδ0 hbound i x
  rw [scalarFlux_eq_slot (I := I) (M := M)]
  simpa only [DifferentialGeometry.Combinatorics.antidiagonalTupleGrid] using
    hjet h T htie hδ_le hδ0 hbound i x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarFlux_jet_grid then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarFlux_jet_grid"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarFlux_jet_grid ``Submission.DifferentialGeometry.Analysis.Spectral.scalarFlux_jet_grid

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
theorem metricDifference_slab
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
        ∀ s ∈ Set.Icc (0 : ℝ) tau,
          ((T : ℝ) - s ∈ D.regular) ∧
          metricCauchySchwarzBound (I := I) (g_fam (T : ℝ))
            (ccTensorBilinSymm (I := I) (g_fam (T : ℝ))
              (metricDifferenceCcTensor (I := I) (M := M)
                (g_fam (T : ℝ)) (g_fam ((T : ℝ) - s)))) (1 / 4 : ℝ) ∧
          ∀ i x,
            riemannianFiberNormSq (I := I) (M := M) (g_fam (T : ℝ)) 0 (2 + i) x
              ((iteratedCovGrad (I := I) (g_fam (T : ℝ)) 0 2 i
                (metricDifferenceCcTensor (I := I) (M := M)
                  (g_fam (T : ℝ)) (g_fam ((T : ℝ) - s)))).toSection x) ≤ B i := by
  classical
  obtain ⟨tau, htau, htau_one, hshort⟩ :=
    lapDiff_short (I := I) (M := M) g_fam hG T
  let q : SmoothRiemannianMetric I M := g_fam (T : ℝ)
  let K : Set ℝ := Set.Icc ((T : ℝ) - tau) (T : ℝ)
  let P : ℝ → SmoothCcTensor q 0 2 := fun t =>
    metricDifferenceCcTensor (I := I) (M := M) q (g_fam t)
  have hK : IsCompact K := by
    simpa only [K] using _root_.CompactIccSpace.isCompact_Icc
  have hKreg : K ⊆ D.regular := by
    intro t ht
    have hs : (T : ℝ) - t ∈ Set.Icc (0 : ℝ) tau := by
      constructor <;> dsimp only [K] at ht <;> linarith [ht.1, ht.2]
    have hreg := (hshort ((T : ℝ) - t) hs).1
    convert hreg using 1
    all_goals ring
  have hPjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      (I.prod 𝓘(ℝ, TensorRSModel 0 2 ℝ E)) ∞
      (fun p : M × ℝ => TotalSpace.mk' (TensorRSModel 0 2 ℝ E)
        (E := fun z : M => TensorRSSpace 0 2 I z) p.1
        ((P p.2).toSection p.1))
      ((Set.univ : Set M) ×ˢ D.regular) := by
    simpa only [P, q] using metricDifference_joint (I := I) (M := M) g_fam hG q
  obtain ⟨B, hB, hjet⟩ := joint_jet_bdd (I := I) (M := M) q 0 2 P
    hK hKreg hPjoint
  refine ⟨tau, htau, htau_one, B, hB, ?_⟩
  intro s hs
  have htK : (T : ℝ) - s ∈ K := by
    change (T : ℝ) - tau ≤ (T : ℝ) - s ∧ (T : ℝ) - s ≤ T
    constructor <;> linarith [hs.1, hs.2]
  have hbound : metricCauchySchwarzBound (I := I) q
      (ccTensorBilinSymm (I := I) q (P ((T : ℝ) - s))) (1 / 4 : ℝ) := by
    intro y v w
    rw [metricDifference_bilin (I := I) (M := M)]
    simpa only [q, sub_apply] using
      (hshort s hs).2 y v w
  refine ⟨(hshort s hs).1, ?_, ?_⟩
  · simpa only [q, P] using hbound
  · intro i x
    simpa only [q, P] using hjet i ((T : ℝ) - s) htK x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.metricDifference_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.metricDifference_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.metricDifference_slab ``Submission.DifferentialGeometry.Analysis.Spectral.metricDifference_slab

omit [SigmaCompactSpace M] in
theorem scalarFlux_slab
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    (T : D.RegularTime) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      ∃ B : ℕ → ℝ, (∀ i, 0 ≤ B i) ∧
        ∀ s ∈ Set.Icc (0 : ℝ) tau, ∀ i x,
          riemannianFiberNormSq (I := I) (M := M) (g_fam (T : ℝ))
              1 (1 + i) x
              ((iteratedCovGrad (I := I) (g_fam (T : ℝ)) 1 1 i
                (scalarFluxCoeff (I := I) (M := M) (g_fam (T : ℝ))
                  (g_fam ((T : ℝ) - s)))).toSection x) ≤
            B i := by
  classical
  obtain ⟨tau, htau, htau_one, J, hJ, hdata⟩ :=
    metricDifference_slab (I := I) (M := M) g_fam hG T
  let q : SmoothRiemannianMetric I M := g_fam (T : ℝ)
  let P : ℝ → SmoothCcTensor q 0 2 := fun t =>
    metricDifferenceCcTensor (I := I) (M := M) q (g_fam t)
  obtain ⟨C, hC, hflux⟩ :=
    scalarFlux_jet_grid (I := I) (M := M) q (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨tau, htau, htau_one, fun i =>
    C i * DifferentialGeometry.Combinatorics.antidiagonalTupleGrid J i,
    fun i => mul_nonneg (hC i)
      (DifferentialGeometry.Combinatorics.antidiagonalTupleGrid_nonneg J hJ i), ?_⟩
  intro s hs i x
  have hsdata := hdata s hs
  have htie : ∀ y v w,
      (g_fam ((T : ℝ) - s)).inner y v w =
        q.inner y v w + ccTensorBilinSymm (I := I) q (P ((T : ℝ) - s)) y v w := by
    intro y v w
    rw [metricDifference_bilin (I := I) (M := M)]
    ring
  have hbound : metricCauchySchwarzBound (I := I) q
      (ccTensorBilinSymm (I := I) q (P ((T : ℝ) - s))) (1 / 4 : ℝ) := by
    simpa only [q, P] using hsdata.2.1
  have hlocal := hflux (g_fam ((T : ℝ) - s)) (P ((T : ℝ) - s)) htie
    (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    hbound i x
  have hgrid :
      DifferentialGeometry.Combinatorics.antidiagonalTupleGrid
          (fun j => riemannianFiberNormSq (I := I) (M := M) q 0 (2 + j) x
            ((iteratedCovGrad (I := I) q 0 2 j (P ((T : ℝ) - s))).toSection x)) i ≤
        DifferentialGeometry.Combinatorics.antidiagonalTupleGrid J i := by
    apply grid_mono
    · intro j
      exact riemannianFiberNormSq_nonneg (I := I) (M := M) q 0 (2 + j) x _
    · intro j
      simpa only [q, P] using hsdata.2.2 j x
  exact hlocal.trans (mul_le_mul_of_nonneg_left hgrid (hC i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Spectral.scalarFlux_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Spectral.scalarFlux_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Spectral.scalarFlux_slab ``Submission.DifferentialGeometry.Analysis.Spectral.scalarFlux_slab

end DifferentialGeometry.Analysis.Spectral

end
