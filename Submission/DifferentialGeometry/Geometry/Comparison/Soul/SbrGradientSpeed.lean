import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrEulerSpeed
import Submission.DifferentialGeometry.Geometry.Comparison.Soul.SbrGradient

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.Topology _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.NNReal
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

private theorem exists_positive_rate_inv_lt
    {r epsilon : ℝ} (hr : 0 < r) (hepsilon : 0 < epsilon) :
    ∃ a0 : ℝ, 0 < a0 ∧ a0 < r ∧ a0⁻¹ < r⁻¹ + epsilon := by
  let b : ℝ := r⁻¹ + epsilon / 2
  have hb : 0 < b := add_pos (inv_pos.mpr hr) (half_pos hepsilon)
  have hrb : r⁻¹ < b := by dsimp only [b]; linarith
  refine ⟨b⁻¹, inv_pos.mpr hb, ?_, ?_⟩
  · simpa only [one_div, inv_inv] using one_div_lt_one_div_of_lt (inv_pos.mpr hr) hrb
  · rw [inv_inv]
    dsimp only [b]
    linarith

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Topology.exists_positive_rate_inv_lt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Topology.exists_positive_rate_inv_lt target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem exists_nearest_superlevel_limit_with_gradient_speed
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (F : M → ℝ) (L : ℝ≥0) (hF : LipschitzWith L F)
    (hconc : ∀ (p : M) (v : TangentSpace I p),
      ConcaveOn ℝ _root_.Set.univ (fun t => F (intrinsicGeodesic g hEnorm p v t)))
    (hC : IsCompact {z : M | 0 ≤ F z})
    {a T m : ℝ} (ha : 0 ≤ a) (haT : a < T) (hTm : T < m)
    (hmax : ∃ q : M, F q = m ∧ ∀ z : M, F z ≤ m)
    (x : M) (hx : F x = a) :
    ∃ eta : ℝ → M,
      LipschitzWith (Real.toNNReal (Metric.diam {z : M | 0 ≤ F z} / (m - T))) eta ∧
      eta a = x ∧ _root_.Set.MapsTo eta (_root_.Set.Icc a T) {z : M | 0 ≤ F z} ∧
      (∀ t ∈ _root_.Set.Icc a T, F (eta t) = t) ∧
      ∀ s ∈ _root_.Set.Ico a T,
        let G := intrinsicGeneralizedGradient g hEnorm hF hconc (eta s)
        G ≠ 0 ∧ 0 < Real.sqrt (g.inner (eta s) G G) ∧
          ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ h in 𝓝[>] (0 : ℝ),
            _root_.Dist.dist (eta (s + h)) (eta s) / h ≤
              (Real.sqrt (g.inner (eta s) G G))⁻¹ + epsilon := by
  obtain ⟨eta, hetaLip, hetaStart, hetaMaps, hetaLevel, hetaSpeed⟩ :=
    exists_nearest_superlevel_limit_with_local_speed
      g hEnorm F L hF hconc hC ha haT hTm hmax x hx
  obtain ⟨q, hq, _hqmax⟩ := hmax
  refine ⟨eta, hetaLip, hetaStart, hetaMaps, hetaLevel, ?_⟩
  intro s hs
  let G := intrinsicGeneralizedGradient g hEnorm hF hconc (eta s)
  let r : ℝ := Real.sqrt (g.inner (eta s) G G)
  have hlt : F (eta s) < F q := by
    rw [hetaLevel s ⟨hs.1, hs.2.le⟩, hq]
    exact hs.2.trans hTm
  have hG : G ≠ 0 := intrinsicGeneralizedGradient_ne_zero_of_lt g hEnorm hF hconc hlt
  have hr : 0 < r :=
    (intrinsicGeneralizedGradient_norm_pos_le_of_lt g hEnorm hF hconc hlt).1
  refine ⟨hG, hr, ?_⟩
  intro epsilon hepsilon
  let U : TangentSpace I (eta s) := r⁻¹ • G
  obtain ⟨hUnorm, hUvalue, _hUmax, _hUunique⟩ :=
    intrinsicGeneralizedGradient_unit_maximizer g hEnorm hF hconc (eta s) hG
  have hunit : g.inner (eta s) U U = 1 := by
    have hsq := Real.sq_sqrt (gInner_self_nonneg g (eta s) U)
    rw [hUnorm, one_pow] at hsq
    exact hsq.symm
  have hvalue : intrinsicRightDerivative g hEnorm F (eta s) U = r := hUvalue
  obtain ⟨a0, ha0, ha0r, ha0inv⟩ := exists_positive_rate_inv_lt hr hepsilon
  obtain ⟨delta, hdelta, hlocal⟩ := hetaSpeed s hs U hunit a0 ha0 (by
    rw [hvalue]
    exact ha0r)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hdelta (sub_pos.mpr hs.2))] with h hh
  have hhdelta : h < delta := hh.2.trans_le (min_le_left _ _)
  have hhT : h < T - s := hh.2.trans_le (min_le_right _ _)
  have hdist := hlocal h hh.1 hhdelta (by linarith)
  have hquot : _root_.Dist.dist (eta (s + h)) (eta s) / h ≤ a0⁻¹ := by
    apply (div_le_iff₀ hh.1).mpr
    simpa only [div_eq_mul_inv, mul_comm] using hdist
  exact hquot.trans ha0inv.le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Topology.exists_nearest_superlevel_limit_with_gradient_speed then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Topology.exists_nearest_superlevel_limit_with_gradient_speed"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Topology.exists_nearest_superlevel_limit_with_gradient_speed ``Submission.DifferentialGeometry.Geometry.Topology.exists_nearest_superlevel_limit_with_gradient_speed

end DifferentialGeometry.Geometry.Topology

end
