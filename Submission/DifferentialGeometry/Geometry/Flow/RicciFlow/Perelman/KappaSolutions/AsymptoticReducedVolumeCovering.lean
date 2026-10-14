import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Covering
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.UpperBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardSliceMass
import Submission.DifferentialGeometry.Topology.Covering.Fiber.FiniteCardinality
import Submission.DifferentialGeometry.Topology.Manifold.LocallyPathConnected

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E H M N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [CompactSpace N] [ConnectedSpace N] {D : RealTimeInterval}

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace N := borel N

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry_1 : BorelSpace N := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

variable [NeZero (Module.finrank ℝ E)]

private theorem redVolume_le_one_of_compact
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (T : ℝ) (x : M) {tau : ℝ} (htau : 0 < tau)
    (hreg : _root_.Set.Icc (T - tau) T ⊆ D.regular) : redVolume S T x tau ≤ 1 := by
  apply redVolume_le_one_of_rm S hS T (RiemannianMetricComplete.of_compact _) x ?_ htau hreg
  intro sigma _ hslab
  obtain ⟨K, _, hK⟩ := exists_curvature_bound_on_closed_interval_of_isSolutionOn S hS hslab
  exact ⟨K, hK⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_le_one_of_compact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.redVolume_le_one_of_compact target :: scope.openDecls } }

theorem natCast_mul_asymptoticReducedVolume_le_one_of_compact_covering
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn S)
    (p : M → N) (hp : IsLocalDiffeomorph I I ∞ p) (hcover : IsCoveringMap p)
    (k : ℕ) (hcard : ∀ y : N, {x : M | p x = y}.encard = (k : ℕ∞))
    (T : ℝ) (hregular : _root_.Set.Iic T ⊆ D.regular)
    (hscalar : ∀ t ≤ T, ∀ y : N, 0 ≤ S.scalar t y) (x : M) :
    (k : ℝ≥0∞) * KappaSolutions.asymptoticReducedVolume S T (p x) ≤ 1 := by
  obtain ⟨C, _, hbound⟩ := exists_redVolume_covering_lower_bound_of_compact
    S hS p hp hcover k hcard T hregular hscalar x
  have hforall (tau : ℝ) (htau : 1 < tau) :
      ENNReal.ofReal (Real.exp (-C / (2 * Real.sqrt tau))) *
        ((k : ℝ≥0∞) * KappaSolutions.asymptoticReducedVolume S T (p x)) ≤ 1 := by
    have hle : KappaSolutions.asymptoticReducedVolume S T (p x) ≤ redVolume S T (p x) tau :=
      iInf_le (fun t : _root_.Set.Ioi (0 : ℝ) => KappaSolutions.intrinsicReducedVolume S T (p x) t)
        ⟨tau, zero_lt_one.trans htau⟩
    apply (mul_le_mul' le_rfl (mul_le_mul' le_rfl hle)).trans
    exact (hbound tau htau).trans (redVolume_le_one_of_compact
      (S.localPullback p hp) (hS.localPullback p hp) T x (zero_lt_one.trans htau)
      (fun _ ht => hregular ht.2))
  have hratio : _root_.Filter.Tendsto (fun r : ℝ => -C / (2 * r)) _root_.Filter.atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num))
  have hfactor : _root_.Filter.Tendsto (fun r : ℝ => ENNReal.ofReal (Real.exp (-C / (2 * r))))
      atTop (𝓝 1) := by
    simpa only [Real.exp_zero, ENNReal.ofReal_one, Function.comp_def] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (Real.continuous_exp.continuousAt.tendsto.comp hratio)
  have hlim := ENNReal.Tendsto.mul_const
    (b := (k : ℝ≥0∞) * KappaSolutions.asymptoticReducedVolume S T (p x))
    hfactor (Or.inl one_ne_zero)
  rw [one_mul] at hlim
  apply le_of_tendsto hlim
  filter_upwards [_root_.Filter.eventually_gt_atTop (1 : ℝ)] with r hr
  have hr0 : 0 ≤ r := zero_le_one.trans hr.le
  have hr2 : 1 < r ^ 2 := by nlinarith
  simpa only [Real.sqrt_sq hr0] using hforall (r ^ 2) hr2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.natCast_mul_asymptoticReducedVolume_le_one_of_compact_covering then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.natCast_mul_asymptoticReducedVolume_le_one_of_compact_covering"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.natCast_mul_asymptoticReducedVolume_le_one_of_compact_covering ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.natCast_mul_asymptoticReducedVolume_le_one_of_compact_covering

end DifferentialGeometry.PDE.RicciFlow.Perelman

end

section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Submission.DifferentialGeometry.Geometry.Curvature

variable {E H M N : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [CompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [CompactSpace N] [ConnectedSpace N] {D : RealTimeInterval}

theorem covering_injective_of_one_half_lt_asymptoticReducedVolume
    (S : SolutionOn (I := I) (M := N) D) (hS : IsSolutionOn S)
    (p : M → N) (hp : IsLocalDiffeomorph I I ∞ p) (hcover : IsCoveringMap p)
    (T : ℝ) (hregular : _root_.Set.Iic T ⊆ D.regular)
    (hscalar : ∀ t ≤ T, ∀ y : N, 0 ≤ S.scalar t y) (x : M)
    (hmass : (1 / 2 : ℝ≥0∞) < KappaSolutions.asymptoticReducedVolume S T (p x)) :
    Function.Injective p := by
  let : LocallyPathConnectedSpace N :=
    Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners I
  let : PathConnectedSpace N := pathConnectedSpace_iff_connectedSpace.mpr inferInstance
  obtain ⟨k, hcard⟩ := Topology.Covering.exists_encard_fiber_eq_natCast_of_compact hcover
  have hbound := natCast_mul_asymptoticReducedVolume_le_one_of_compact_covering
    S hS p hp hcover k hcard T hregular hscalar x
  have hk : k ≤ 1 := by
    by_contra hnot
    have hk2 : 2 ≤ k := by omega
    have hk2' : (2 : ℝ≥0∞) ≤ k := by exact_mod_cast hk2
    have hlt := ENNReal.mul_lt_mul_right (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hmass
    have htwo : (2 : ℝ≥0∞) * (1 / 2) = 1 := by
      simpa only [one_div] using ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    rw [htwo] at hlt
    exact (not_lt_of_ge hbound) (hlt.trans_le (mul_le_mul' hk2' le_rfl))
  intro y z hyz
  have hsmall : {w : M | p w = p y}.encard ≤ 1 := by
    rw [hcard]
    exact_mod_cast hk
  exact Set.encard_le_one_iff.mp hsmall y z rfl hyz.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.covering_injective_of_one_half_lt_asymptoticReducedVolume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.covering_injective_of_one_half_lt_asymptoticReducedVolume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.covering_injective_of_one_half_lt_asymptoticReducedVolume ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.covering_injective_of_one_half_lt_asymptoticReducedVolume

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
