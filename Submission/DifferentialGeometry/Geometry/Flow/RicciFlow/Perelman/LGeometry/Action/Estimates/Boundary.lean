import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Estimates.Curvature
import Submission.DifferentialGeometry.Topology.FirstExit

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem lRegularizedAction_ge_of_scalar_lower_on_interior
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (α : ℝ → M)
    {a b v B : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbv : b ≤ v) (hB : 0 ≤ B)
    (hscalar : ∀ s ∈ _root_.Set.Ioo a b, -B ≤ S.scalar (T - s ^ 2) (α s))
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T α) _root_.MeasureTheory.MeasureSpace.volume a b) :
    -(2 * B * v ^ 2) * (b - a) ≤ lRegularizedAction S T α a b := by
  let C := -(2 * B * v ^ 2)
  have hh := intervalIntegral.integral_mono_on_of_le_Ioo hab
    (intervalIntegrable_const (c := C)) hLag (fun s hs => ?_)
  · simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm, lRegularizedAction, C] using hh
  have hs2 : s ^ 2 ≤ v ^ 2 :=
    (sq_le_sq₀ (ha.trans hs.1.le) (ha.trans (hab.trans hbv))).mpr (hs.2.le.trans hbv)
  have hsc := mul_le_mul_of_nonneg_left (hscalar s hs) (by positivity : 0 ≤ 2 * s ^ 2)
  have hsq := mul_le_mul_of_nonneg_left hs2 (by positivity : 0 ≤ 2 * B)
  have hkin := metric_inner_self_nonneg (S.base.metric (T - s ^ 2)) (α s) (lVelocity α s)
  dsimp only [C, lRegularizedLagrangian]
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_scalar_lower_on_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_scalar_lower_on_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_scalar_lower_on_interior ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_scalar_lower_on_interior

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedAction_ge_of_subinterval_separation
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (α : ℝ → M)
    {a b c d v μ B r : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hcd : c < d)
    (hdb : d ≤ b) (hbv : b ≤ v) (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (g : SmoothRiemannianMetric I M)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) I 1 α (_root_.Set.Icc a b))
    (hmetric : ∀ s ∈ _root_.Set.Ioo c d,
      μ * g.inner (α s) (lVelocity (I := I) α s) (lVelocity (I := I) α s) ≤
        (S.base.metric (T - s ^ 2)).inner (α s)
          (lVelocity (I := I) α s) (lVelocity (I := I) α s))
    (hscalar : ∀ s ∈ _root_.Set.Ioo a b, -B ≤ S.scalar (T - s ^ 2) (α s))
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T α) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hseparation : ENNReal.ofReal r ≤ riemannianEDistOf g (α c) (α d)) :
    μ * r ^ 2 / (2 * (b - a)) - 2 * B * v ^ 2 * (b - a) ≤
      lRegularizedAction S T α a b := by
  have hab : a < b := lt_of_le_of_lt hac (hcd.trans_le hdb)
  have hcb : c ≤ b := hcd.le.trans hdb
  have had : a ≤ d := hac.trans hcd.le
  have hi (s t : ℝ) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b) :
      IntervalIntegrable (lRegularizedLagrangian S T α) _root_.MeasureTheory.MeasureSpace.volume s t :=
    hLag.mono_set (by simpa only [_root_.Set.uIcc_of_le hst, _root_.Set.uIcc_of_le hab.le] using _root_.Set.Icc_subset_Icc has htb)
  have hleft := lRegularizedAction_ge_of_scalar_lower_on_interior S T α ha hac
    (hcb.trans hbv) hB (fun s hs => hscalar s ⟨hs.1, hs.2.trans_le hcb⟩)
    (hi a c le_rfl hac hcb)
  have hmiddle := lRegularizedAction_ge_of_endpoint_separation_of_interior_bounds S T α
    (ha.trans hac) hcd (hdb.trans hbv) hμ hB hr g (hα.mono (_root_.Set.Icc_subset_Icc hac hdb))
    hmetric (fun s hs => hscalar s ⟨lt_of_le_of_lt hac hs.1, hs.2.trans_le hdb⟩)
    (hi c d hac hcd.le hdb) hseparation
  have hright := lRegularizedAction_ge_of_scalar_lower_on_interior S T α (ha.trans had)
    hdb hbv hB (fun s hs => hscalar s ⟨lt_of_le_of_lt had hs.1, hs.2⟩)
    (hi d b had hdb le_rfl)
  have hadd₁ := lRegularizedAction_add S T α a c d
    (hi a c le_rfl hac hcb) (hi c d hac hcd.le hdb)
  have hadd₂ := lRegularizedAction_add S T α a d b
    (hi a d le_rfl had hdb) (hi d b had hdb le_rfl)
  have hratio : μ * r ^ 2 / (2 * (b - a)) ≤ μ * r ^ 2 / (2 * (d - c)) :=
    div_le_div_of_nonneg_left (mul_nonneg hμ (sq_nonneg r))
      (by linarith) (by linarith)
  nlinarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_subinterval_separation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_subinterval_separation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_subinterval_separation ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_subinterval_separation

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedAction_ge_of_leaves_closed_set
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (α : ℝ → M)
    {a b v μ B r : ℝ} (ha : 0 ≤ a) (hbv : b ≤ v)
    (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsClosed K)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) I 1 α (_root_.Set.Icc a b))
    (hstart : α a ∈ interior K)
    (hmetric : ∀ s ∈ _root_.Set.Ioo a b, α s ∈ K →
      μ * g.inner (α s) (lVelocity (I := I) α s) (lVelocity (I := I) α s) ≤
        (S.base.metric (T - s ^ 2)).inner (α s)
          (lVelocity (I := I) α s) (lVelocity (I := I) α s))
    (hscalar : ∀ s ∈ _root_.Set.Ioo a b, -B ≤ S.scalar (T - s ^ 2) (α s))
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T α) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hfront : ∀ y ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g (α a) y)
    (hexit : ¬ _root_.Set.MapsTo α (_root_.Set.Icc a b) K) :
    μ * r ^ 2 / (2 * (b - a)) - 2 * B * v ^ 2 * (b - a) ≤
      lRegularizedAction S T α a b := by
  obtain ⟨t, ht, hstay, htfront⟩ :=
    exists_first_exit_frontier_Icc_of_not_mapsTo hK hα.continuousOn hstart hexit
  apply lRegularizedAction_ge_of_subinterval_separation S T α ha le_rfl ht.1 ht.2.le
    hbv hμ hB hr g hα ?_ hscalar hLag (hfront _ htfront)
  intro s hs
  exact hmetric s ⟨hs.1, hs.2.trans_le ht.2.le⟩ (hstay ⟨hs.1.le, hs.2.le⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_leaves_closed_set then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_leaves_closed_set"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_leaves_closed_set ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_leaves_closed_set

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedAction_ge_of_enters_closed_set
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (α : ℝ → M)
    {a b v μ B r : ℝ} (ha : 0 ≤ a) (hbv : b ≤ v)
    (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (g : SmoothRiemannianMetric I M) {K : Set M} (hK : IsClosed K)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) I 1 α (_root_.Set.Icc a b))
    (hend : α b ∈ interior K)
    (hmetric : ∀ s ∈ _root_.Set.Ioo a b, α s ∈ K →
      μ * g.inner (α s) (lVelocity (I := I) α s) (lVelocity (I := I) α s) ≤
        (S.base.metric (T - s ^ 2)).inner (α s)
          (lVelocity (I := I) α s) (lVelocity (I := I) α s))
    (hscalar : ∀ s ∈ _root_.Set.Ioo a b, -B ≤ S.scalar (T - s ^ 2) (α s))
    (hLag : IntervalIntegrable (lRegularizedLagrangian S T α) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hfront : ∀ y ∈ frontier K, ENNReal.ofReal r ≤ riemannianEDistOf g y (α b))
    (hexit : ¬ _root_.Set.MapsTo α (_root_.Set.Icc a b) K) :
    μ * r ^ 2 / (2 * (b - a)) - 2 * B * v ^ 2 * (b - a) ≤
      lRegularizedAction S T α a b := by
  obtain ⟨t, ht, hstay, htfront⟩ :=
    exists_last_entry_frontier_Icc_of_not_mapsTo hK hα.continuousOn hend hexit
  apply lRegularizedAction_ge_of_subinterval_separation S T α ha ht.1.le ht.2 le_rfl
    hbv hμ hB hr g hα ?_ hscalar hLag (hfront _ htfront)
  intro s hs
  exact hmetric s ⟨lt_of_le_of_lt ht.1.le hs.1, hs.2⟩ (hstay ⟨hs.1.le, hs.2.le⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_enters_closed_set then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_enters_closed_set"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_enters_closed_set ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_ge_of_enters_closed_set

theorem lRegularizedAction_prefix_le_of_action_le
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (α : ℝ → M)
    {a d b v A B : ℝ} (ha : 0 ≤ a) (had : a ≤ d) (hdb : d ≤ b) (hbv : b ≤ v)
    (hB : 0 ≤ B)
    (hscalar : ∀ t ∈ _root_.Set.Ioo d b, -B ≤ S.scalar (T - t ^ 2) (α t))
    (hint : IntervalIntegrable (lRegularizedLagrangian S T α) _root_.MeasureTheory.MeasureSpace.volume a b)
    (hact : lRegularizedAction S T α a b ≤ A) :
    lRegularizedAction S T α a d ≤ A + 2 * B * v ^ 2 * (b - d) := by
  have hab := had.trans hdb
  have hleft := hint.mono_set (by
    rw [_root_.Set.uIcc_of_le had, _root_.Set.uIcc_of_le hab]
    exact _root_.Set.Icc_subset_Icc le_rfl hdb)
  have hright := hint.mono_set (by
    rw [_root_.Set.uIcc_of_le hdb, _root_.Set.uIcc_of_le hab]
    exact _root_.Set.Icc_subset_Icc had le_rfl)
  have htail := lRegularizedAction_ge_of_scalar_lower_on_interior S T α
    (ha.trans had) hdb hbv hB hscalar hright
  have hadd := lRegularizedAction_add S T α a d b hleft hright
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_prefix_le_of_action_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_prefix_le_of_action_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_prefix_le_of_action_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_prefix_le_of_action_le

end DifferentialGeometry.PDE.RicciFlow.Perelman
