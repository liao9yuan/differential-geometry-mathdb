import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardForwardMixedJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.BackwardForwardUniformJets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.Filter
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology


theorem backwardForwardErrorJet_control
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (c : ℝ) (hc : (1 : ℝ) / 2 ≤ c)
    (J : ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    (hcoeff : ∀ q ≤ Nat.ceil epsilon⁻¹, |c * (-c⁻¹) ^ q| ≤ 2)
    (hmodel : |c - 1| * (3 * Real.sqrt 3) ≤ epsilon / 4)
    (hclose : ∀ a q : ℕ, a + 2 * q ≤ Nat.ceil epsilon⁻¹ →
      ∀ theta ∈ _root_.Set.Icc (1 : ℝ) 3, ∀ x ∈ spatialNeckClosedCore epsilon,
        tensor02CovDerivNormWith a (J q theta)
          (strongNeckBackgroundMetric epsilon (1 - theta))
          (strongNeckBackgroundMetric epsilon (1 - theta)) x ≤
            epsilon / (8 * _root_.Max.max 1 (Real.sqrt ((3 : ℝ) ^ (Nat.ceil epsilon⁻¹ + 2))))) :
    StrongNeckJetControl epsilon (backwardForwardErrorJet epsilon c J) := by
  let K : ℝ := _root_.Max.max 1 (Real.sqrt ((3 : ℝ) ^ (Nat.ceil epsilon⁻¹ + 2)))
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hbudget : (2 * K) * (epsilon / (8 * K)) = epsilon / 4 := by
    field_simp [hK.ne']
    ring
  refine ⟨epsilon / 2, by positivity, by linarith, ?_⟩
  intro a q haq s hs x hx
  have hao : a ≤ Nat.ceil epsilon⁻¹ := by omega
  have hqo : q ≤ Nat.ceil epsilon⁻¹ := by omega
  have hrank : Real.sqrt ((3 : ℝ) ^ (a + 2)) ≤ K :=
    (Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
      (Nat.add_le_add_right hao 2))).trans (le_max_right _ _)
  have hfactor : |c * (-c⁻¹) ^ q| * Real.sqrt ((3 : ℝ) ^ (a + 2)) ≤ 2 * K :=
    mul_le_mul (hcoeff q hqo) hrank (Real.sqrt_nonneg _) (by norm_num)
  have herror := hclose a q haq (1 - s / c) (backwardForward_time_mapsTo hc hs) x hx
  have hfirst :
      (|c * (-c⁻¹) ^ q| * Real.sqrt ((3 : ℝ) ^ (a + 2))) *
        tensor02CovDerivNormWith a (J q (1 - s / c))
          (strongNeckBackgroundMetric epsilon (1 - (1 - s / c)))
          (strongNeckBackgroundMetric epsilon (1 - (1 - s / c))) x ≤ epsilon / 4 := by
    apply (mul_le_mul hfactor herror (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) hK.le)).trans_eq
    exact hbudget
  exact (backwardForwardErrorJet_covNorm_le epsilon c hc J a q s hs x).trans
    ((add_le_add hfirst hmodel).trans_eq (by ring))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_control then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_control"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_control ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_control


theorem backwardForwardErrorJet_eventually_control
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (J : ℕ → ℕ → ℝ → Tensor0SField (I := SpatialNeckCylinderModel)
      (M := spatialNeckBuffer epsilon) (n := ∞) 2)
    {c : ℕ → ℝ} (hc : _root_.Filter.Tendsto c _root_.Filter.atTop (𝓝 (1 : ℝ)))
    (hconv : ∀ eta : ℝ, 0 < eta → ∀ᶠ i in _root_.Filter.atTop,
      ∀ a q : ℕ, a + 2 * q ≤ Nat.ceil epsilon⁻¹ →
      ∀ theta ∈ _root_.Set.Icc (1 : ℝ) 3, ∀ x ∈ spatialNeckClosedCore epsilon,
        tensor02CovDerivNormWith a (J i q theta)
          (strongNeckBackgroundMetric epsilon (1 - theta))
          (strongNeckBackgroundMetric epsilon (1 - theta)) x ≤ eta) :
    ∀ᶠ i in _root_.Filter.atTop,
      StrongNeckJetControl epsilon (backwardForwardErrorJet epsilon (c i) (J i)) := by
  let order := Nat.ceil epsilon⁻¹
  let K : ℝ := _root_.Max.max 1 (Real.sqrt ((3 : ℝ) ^ (order + 2)))
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hhalf : ∀ᶠ i in _root_.Filter.atTop, (1 : ℝ) / 2 ≤ c i :=
    ((tendsto_order.1 hc).1 (1 / 2) (by norm_num)).mono fun _ hi => hi.le
  have hcoeff (q : ℕ) : ∀ᶠ i in _root_.Filter.atTop, |c i * (-(c i)⁻¹) ^ q| ≤ 2 := by
    have hlim : _root_.Filter.Tendsto (fun i => |c i * (-(c i)⁻¹) ^ q|) _root_.Filter.atTop (𝓝 (1 : ℝ)) := by
      simpa only [abs_pow, abs_neg, abs_one, one_pow] using
        (backwardForward_jet_coefficient_tendsto hc q).abs
    exact ((tendsto_order.1 hlim).2 2 (by norm_num)).mono fun _ hi => hi.le
  have hcoeffs : ∀ᶠ i in _root_.Filter.atTop,
      ∀ q ∈ Finset.range (order + 1), |c i * (-(c i)⁻¹) ^ q| ≤ 2 :=
    (_root_.Filter.eventually_all_finset (Finset.range (order + 1))).2 (fun q _hq => hcoeff q)
  have hmodelLimit : _root_.Filter.Tendsto (fun i => |c i - 1| * (3 * Real.sqrt 3)) _root_.Filter.atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, abs_zero, _root_.MulZeroClass.zero_mul] using
      ((hc.sub_const 1).abs.mul_const (3 * Real.sqrt 3))
  have hmodel : ∀ᶠ i in _root_.Filter.atTop, |c i - 1| * (3 * Real.sqrt 3) ≤ epsilon / 4 :=
    ((tendsto_order.1 hmodelLimit).2 (epsilon / 4) (by positivity)).mono fun _ hi => hi.le
  have heta : 0 < epsilon / (8 * K) := div_pos hepsilon (mul_pos (by norm_num) hK)
  filter_upwards [hhalf, hcoeffs, hmodel, hconv (epsilon / (8 * K)) heta]
    with i hhalf_i hcoeff_i hmodel_i hconv_i
  apply backwardForwardErrorJet_control epsilon hepsilon (c i) hhalf_i (J i) ?_ hmodel_i hconv_i
  intro q hq
  exact hcoeff_i q (Finset.mem_range.mpr (by dsimp only [order]; omega))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_eventually_control then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_eventually_control"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_eventually_control ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.backwardForwardErrorJet_eventually_control

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
