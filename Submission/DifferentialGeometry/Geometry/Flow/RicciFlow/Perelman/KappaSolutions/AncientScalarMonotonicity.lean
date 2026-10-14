import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCurvatureBounds
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TensorNormFinrankNeZero
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TraceCorollaries
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.TerminalMetricLowerBound
import Submission.DifferentialGeometry.Geometry.Curvature.Bounds.RicciUpper
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientTerminalBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

section

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution

open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.Submission.Set
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} {F : PointedFlowData.{u, uE, uH} (I := I) D}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instTopologicalSpaceM : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instTopologicalSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instTopologicalSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instChartedSpaceM : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instChartedSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instChartedSpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instIsManifoldRealSomeENatTopM : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instIsManifoldRealSomeENatTopM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instIsManifoldRealSomeENatTopM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instIsManifoldRealOfNatWithTopENatM : IsManifold I 1 F.M := IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instIsManifoldRealOfNatWithTopENatM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instIsManifoldRealOfNatWithTopENatM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instT2SpaceM : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instT2SpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instT2SpaceM target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instSigmaCompactSpaceM : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instSigmaCompactSpaceM
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.instSigmaCompactSpaceM target :: scope.openDecls } }

theorem scalar_monotoneOn {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (x : F.M) :
    MonotoneOn (fun t : ℝ => F.S.scalar t x) (_root_.Set.Iic 0) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    obtain ⟨t, ht, y, hy⟩ := hF.notFlat
    exact finrank_ne_zero_of_normSq0S_ne_zero (F.S.base.metric t) y (by norm_num : 0 < 4)
      (F.S.base.rm04 t y) hy⟩
  have hcomplete : ∀ t ∈ D.regular,
      RiemannianMetricComplete (I := I) (F.S.base.metric t) :=
    fun t ht => ⟨hF.complete t (D.regular_subset ht)⟩
  obtain ⟨K, hK⟩ := hF.exists_rmNormSq_le
  have hcurv : ∀ a b : ℝ, _root_.Set.Icc a b ⊆ D.regular →
      ∃ C : ℝ, ∀ t ∈ _root_.Set.Icc a b, ∀ y : F.M,
        normSq0S (I := I) (F.S.base.metric t) y 4 (F.S.base.rm04 t y) ≤ C := by
    intro a b hab
    exact ⟨K, fun t ht y => hK t (D.regular_subset (hab ht)) y⟩
  have hR : ∀ t ∈ D.regular, ∀ y : F.M,
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) y ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    intro t ht y
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hF.nonnegativeCurvatureOperator t (D.regular_subset ht) y n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  have hcont : ContinuousOn (fun t : ℝ => F.S.scalar t x) (_root_.Set.Iic 0) := by
    have hmap : Continuous (fun t : ℝ => (t, x)) := continuous_id.prodMk continuous_const
    have h := F.isSolution.scalarCont.comp hmap.continuousOn
      (fun t (ht : t ∈ _root_.Set.Iic (0 : ℝ)) => ⟨by simpa only [hF.carrier_eq] using ht, _root_.Set.mem_univ x⟩)
    simpa only [Function.comp_def] using h
  apply monotoneOn_of_deriv_nonneg (convex_Iic 0) hcont
  · intro t ht
    have htreg : t ∈ D.regular := by
      simpa only [hF.regular_eq, interior_Iic, _root_.Set.mem_Iio] using ht
    exact ((F.isSolution.scalarTime (K := D.carrier)
      (D.regular_subset htreg) (fun _ hs => hs) x).differentiableAt
        (D.regular_mem_nhds htreg)).differentiableWithinAt
  · intro t ht
    have ht0 : t < 0 := by simpa only [interior_Iic, _root_.Set.mem_Iio] using ht
    exact hamilton_ancient_scalar_deriv_nonneg F.S F.isSolution hcomplete hcurv hR
      (fun r hr => by simpa only [hF.regular_eq, _root_.Set.mem_Iio] using hr.trans_lt ht0) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.scalar_monotoneOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.scalar_monotoneOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.scalar_monotoneOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.scalar_monotoneOn

theorem metric_inner_le_exp_scalar_bound {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F)
    {a b C : ℝ} (hab : a ≤ b) (hb : b ≤ 0)
    (x : F.M) (hC : F.S.scalar b x ≤ C) (v : TangentSpace I x) :
    (F.S.base.metric a).inner x v v ≤
      Real.exp (C * (b - a)) * (F.S.base.metric b).inner x v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hslab : _root_.Set.Icc a b ⊆ D.carrier := by
    intro t ht
    simpa only [hF.carrier_eq, _root_.Set.mem_Iic] using ht.2.trans hb
  have hreg : _root_.Set.Ioo a b ⊆ D.regular := by
    intro t ht
    simpa only [hF.regular_eq, _root_.Set.mem_Iio] using ht.2.trans_le hb
  have hRic : ∀ t ∈ _root_.Set.Ioo a b, ∀ y ∈ ({x} : Set F.M), ∀ w : TangentSpace I y,
      F.S.ricciAt t y (vec2 w w) ≤ (C / 2) * (F.S.base.metric t).inner y w w := by
    intro t ht y hy w
    have hyx : y = x := mem_singleton_iff.mp hy
    subst y
    have ht0 : t ≤ 0 := ht.2.le.trans hb
    have hR : F.S.scalar t x ≤ C := (hF.scalar_monotoneOn x ht0 hb ht.2.le).trans hC
    have hcone : metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (I := I) (F.S.base.metric t) x).mpr
      intro n c u w
      have htcar : t ∈ D.carrier := by simpa only [hF.carrier_eq, _root_.Set.mem_Iic] using ht0
      simpa only [SolutionFamily.rm04, metricRm04StandardAt_apply, metricRm04_apply] using
        hF.nonnegativeCurvatureOperator t htcar x n c u w
    have hupper := metricRicciAt_le_half_scalar_mul_inner_of_curvatureOperator_nonnegative
      (F.S.base.metric t) x hcone w
    exact hupper.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hR (by norm_num))
      (metric_inner_self_nonneg (F.S.base.metric t) x w))
  have hraw := metric_inner_lower_bound_of_ricci_upper_interior F.S F.isSolution
    hab hslab hreg hRic (_root_.Set.mem_singleton x) v
  have heq : 2 * (C / 2) * (b - a) = C * (b - a) := by ring
  rw [heq] at hraw
  calc
    (F.S.base.metric a).inner x v v =
        Real.exp (C * (b - a)) *
          (Real.exp (-(C * (b - a))) * (F.S.base.metric a).inner x v v) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp only [add_neg_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (C * (b - a)) * (F.S.base.metric b).inner x v v :=
      mul_le_mul_of_nonneg_left hraw (Real.exp_pos _).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.metric_inner_le_exp_scalar_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.metric_inner_le_exp_scalar_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.metric_inner_le_exp_scalar_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution.metric_inner_le_exp_scalar_bound

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.IsAncientKappaSolution

end

end

section

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

private local instance ancientScalarTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarTopology target :: scope.openDecls } }
private local instance ancientScalarCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarCharted target :: scope.openDecls } }
private local instance ancientScalarSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarSmooth target :: scope.openDecls } }
private local instance ancientScalarC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarC1 target :: scope.openDecls } }
private local instance ancientScalarT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarT2 target :: scope.openDecls } }
private local instance ancientScalarTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarTangentT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarTangentT2 target :: scope.openDecls } }
private local instance ancientScalarSigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarSigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientScalarSigma target :: scope.openDecls } }

theorem ancientKappa_scalar_monotoneOn
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (x : F.M) :
    MonotoneOn (fun t : ℝ => F.S.scalar t x) (Set.Iic 0) := by
  exact CanonicalNeighborhood.IsAncientKappaSolution.scalar_monotoneOn hF x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_monotoneOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_monotoneOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_monotoneOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancientKappa_scalar_monotoneOn

theorem exists_eventually_scalar_pos_of_ancient
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) :
    ∃ x : F.M, ∀ᶠ T in 𝓝[≤] (0 : ℝ), 0 < F.S.scalar T x := by
  obtain ⟨t, ht, x, hx⟩ := hF.notFlat
  have hnonneg : 0 ≤ F.rmNormSq (I := I) t x := by
    exact DifferentialGeometry.Tensor0SBundle.normSq0S_nonneg
      (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x)
  have hpos : 0 < F.S.scalar t x :=
    pos_of_mul_pos_right ((Real.sqrt_pos.mpr (lt_of_le_of_ne hnonneg hx.symm)).trans_le
      (ancientKappa_rmNormLeScalar_finrank F hF t ht x)) (sq_nonneg _)
  have ht0 : t ≤ 0 := by simpa only [hF.carrier_eq, _root_.Set.mem_Iic] using ht
  have hzero : 0 < F.S.scalar 0 x := hpos.trans_le
    (ancientKappa_scalar_monotoneOn F hF x ht0 (mem_Iic.mpr le_rfl) ht0)
  have hc : ContinuousOn (fun T : ℝ => F.S.scalar T x) (_root_.Set.Iic 0) := by
    have hmap : Continuous (fun T : ℝ => (T, x)) := continuous_id.prodMk continuous_const
    have hm : _root_.Set.MapsTo (fun T : ℝ => (T, x)) (_root_.Set.Iic 0) (D.carrier ×ˢ _root_.Set.univ) := by
      intro T hT
      exact ⟨by simpa only [hF.carrier_eq, _root_.Set.mem_Iic] using hT, _root_.Set.mem_univ x⟩
    have hh := F.isSolution.scalarCont.comp hmap.continuousOn hm
    exact hh
  exact ⟨x, (hc 0 (mem_Iic.mpr le_rfl)).eventually (Ioi_mem_nhds hzero)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_scalar_pos_of_ancient then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_scalar_pos_of_ancient"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_scalar_pos_of_ancient ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.exists_eventually_scalar_pos_of_ancient

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end

end
