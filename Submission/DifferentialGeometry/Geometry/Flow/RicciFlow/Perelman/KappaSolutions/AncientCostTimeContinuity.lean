import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostTimeLowerBound
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCostTimeUpperBound
import Mathlib.Topology.Order.LeftRight

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

private local instance topology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.topology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.topology target :: scope.openDecls } }
private local instance charted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.charted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.charted target :: scope.openDecls } }
private local instance smooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.smooth target :: scope.openDecls } }
private local instance t2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.t2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.t2 target :: scope.openDecls } }
private local instance sigma : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sigma
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.sigma target :: scope.openDecls } }

theorem ancient_lCost_continuousOn
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p q : F.M) :
    ContinuousOn (fun b ↦ lCost F.S 0 p q (b ^ 2)) (_root_.Set.Ioi 0) := by
  let f : ℝ → ℝ := fun b ↦ lCost F.S 0 p q (b ^ 2)
  let k : ℝ → ℝ → ℝ := fun a b ↦
    1 + (Real.sqrt (2 * a) * Real.sqrt 3 / (2 * a)) *
      Real.sqrt (b - a) * Real.sqrt 2
  have hf : ∀ a, 0 < a → 0 ≤ f a := by
    intro a ha
    obtain ⟨C, hC⟩ := hF.globalScalarBound
    apply lCost_nonneg_of_scalar_nonneg F.S 0 (sq_nonneg a)
    intro r hr x
    exact (hC (0 - r) (by
      simpa only [ancientTimeInterval_carrier, _root_.Set.mem_Iic, zero_sub] using
        neg_nonpos.mpr hr.1) x).1
  have hk : ∀ a, 0 < a → ∀ b, 0 < k a b := by
    intro a ha b
    dsimp only [k]
    positivity
  have hkdiag : ∀ a, k a a = 1 := by
    intro a
    simp only [k, sub_self, Real.sqrt_zero, _root_.MulZeroClass.mul_zero, _root_.MulZeroClass.zero_mul, add_zero]
  have hlower : ∀ a, 0 < a → ∀ b, a ≤ b → f a ≤ (k a b) ^ 2 * f b := by
    intro a ha b hab
    have hb : 0 < b := ha.trans_le hab
    have hroot : Real.sqrt (f a) ≤ k a b * Real.sqrt (f b) :=
      ancient_sqrt_lCost_le_mul_of_le F hF p q ha hab
    have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg (f a))
      (mul_nonneg (hk a ha b).le (Real.sqrt_nonneg (f b)))).mpr hroot
    simpa only [mul_pow, Real.sq_sqrt (hf a ha), Real.sq_sqrt (hf b hb)] using hsquare
  have hupper : ∀ a, 0 < a → ∀ b, a ≤ b → a ^ 3 * f b ≤ b ^ 3 * f a := by
    intro a ha b hab
    exact ancient_lCost_mul_cube_le_of_le F hF p q ha hab
  intro a ha
  change 0 < a at ha
  change ContinuousWithinAt f (_root_.Set.Ioi 0) a
  apply ContinuousAt.continuousWithinAt
  apply continuousAt_iff_continuous_left_right.mpr
  constructor
  · have hleftK : ContinuousAt (fun t ↦ k t a) a := by
      dsimp only [k]
      fun_prop (disch := positivity)
    have hlo : ContinuousAt (fun t ↦ t ^ 3 * f a / a ^ 3) a := by fun_prop
    have hhi : ContinuousAt (fun t ↦ (k t a) ^ 2 * f a) a :=
      (hleftK.pow 2).mul continuousAt_const
    have hloValue : a ^ 3 * f a / a ^ 3 = f a := by field_simp [ha.ne']
    have hhiValue : (k a a) ^ 2 * f a = f a := by rw [hkdiag]; norm_num
    have hloLim : _root_.Filter.Tendsto (fun t ↦ t ^ 3 * f a / a ^ 3)
        (𝓝[≤] a) (𝓝 (f a)) := by
      simpa only [ContinuousWithinAt, hloValue] using
        (hlo.continuousWithinAt : ContinuousWithinAt
          (fun t ↦ t ^ 3 * f a / a ^ 3) (_root_.Set.Iic a) a)
    have hhiLim : _root_.Filter.Tendsto (fun t ↦ (k t a) ^ 2 * f a)
        (𝓝[≤] a) (𝓝 (f a)) := by
      simpa only [ContinuousWithinAt, hhiValue] using
        (hhi.continuousWithinAt : ContinuousWithinAt
          (fun t ↦ (k t a) ^ 2 * f a) (_root_.Set.Iic a) a)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hloLim hhiLim
    · filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds ha)] with t hta ht
      apply (div_le_iff₀ (pow_pos ha 3)).mpr
      simpa only [mul_comm] using hupper t ht a hta
    · filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Ioi_mem_nhds ha)] with t hta ht
      exact hlower t ht a hta
  · have hrightK : ContinuousAt (fun t ↦ k a t) a := by
      dsimp only [k]
      fun_prop
    have hlo : ContinuousAt (fun t ↦ f a / (k a t) ^ 2) a :=
      continuousAt_const.div (hrightK.pow 2) (by rw [hkdiag]; norm_num)
    have hhi : ContinuousAt (fun t ↦ t ^ 3 * f a / a ^ 3) a := by fun_prop
    have hloValue : f a / (k a a) ^ 2 = f a := by rw [hkdiag]; norm_num
    have hhiValue : a ^ 3 * f a / a ^ 3 = f a := by field_simp [ha.ne']
    have hloLim : _root_.Filter.Tendsto (fun t ↦ f a / (k a t) ^ 2)
        (𝓝[≥] a) (𝓝 (f a)) := by
      simpa only [ContinuousWithinAt, hloValue] using
        (hlo.continuousWithinAt : ContinuousWithinAt
          (fun t ↦ f a / (k a t) ^ 2) (_root_.Set.Ici a) a)
    have hhiLim : _root_.Filter.Tendsto (fun t ↦ t ^ 3 * f a / a ^ 3)
        (𝓝[≥] a) (𝓝 (f a)) := by
      simpa only [ContinuousWithinAt, hhiValue] using
        (hhi.continuousWithinAt : ContinuousWithinAt
          (fun t ↦ t ^ 3 * f a / a ^ 3) (_root_.Set.Ici a) a)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hloLim hhiLim
    · filter_upwards [self_mem_nhdsWithin] with t hat
      apply (div_le_iff₀ (sq_pos_of_pos (hk a ha t))).mpr
      simpa only [mul_comm] using hlower a ha t hat
    · filter_upwards [self_mem_nhdsWithin] with t hat
      apply (le_div_iff₀ (pow_pos ha 3)).mpr
      simpa only [mul_comm] using hupper a ha t hat

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_continuousOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_continuousOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_continuousOn ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_lCost_continuousOn

theorem ancient_redLength_continuousOn_time
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F) (p q : F.M) :
    ContinuousOn (fun tau ↦ redLength F.S 0 p q tau) (_root_.Set.Ioi 0) := by
  have hcost : ContinuousOn (fun tau ↦ lCost F.S 0 p q tau) (_root_.Set.Ioi 0) := by
    have hcomp := (ancient_lCost_continuousOn F hF p q).comp
      Real.continuous_sqrt.continuousOn (fun t ht ↦ Real.sqrt_pos.mpr ht)
    apply hcomp.congr
    intro t ht
    have htpos : 0 < t := ht
    simp only [Function.comp_apply, Real.sq_sqrt htpos.le]
  exact hcost.div (continuousOn_const.mul Real.continuous_sqrt.continuousOn)
    (fun t ht ↦ mul_ne_zero (by norm_num) (Real.sqrt_pos.mpr ht).ne')

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_continuousOn_time then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_continuousOn_time"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_continuousOn_time ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ancient_redLength_continuousOn_time

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
