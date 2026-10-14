import Submission.DifferentialGeometry.Geometry.Comparison.Toponogov.RadialNets

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Filter _root_.Set
open scoped _root_.Topology

namespace DifferentialGeometry.Toponogov

variable {X : Type*} [MetricSpace X] {ι : Type*} {z : X}
  {L : ι → ℝ} {gamma : ι → ℝ → X}

theorem exists_finset_radial_cone_approximation
    (hrad : IsRadialFamily z L gamma) (hL : ∀ i, 0 < L i)
    (hmin : ∀ i, ∀ s ∈ _root_.Set.Ioc 0 (L i), ∀ t ∈ _root_.Set.Ioc 0 (L i), _root_.Dist.dist (gamma i s) (gamma i t) = |s - t|)
    (hmono : ∀ i j, CoordinatewiseNonincreasingOn (L i) (L j) (radialComparisonAngle gamma i j))
    (K : AngleKernel ι) (hK : ∀ i j, K.angle i j = limitingRadialAngle L gamma i j)
    (htb : let _ := K.metricSpace; TotallyBounded (_root_.Set.univ : Set (Quotient K.setoid)))
    {a b eps : ℝ} (ha : 0 < a) (hab : a ≤ b) (heps : 0 < eps)
    (P : Finset (ι × ℝ)) (hP : ∀ p ∈ P, p.2 ∈ _root_.Set.Icc a b) :
    let _ := K.metricSpace
    ∃ S : Finset (ι × ℝ), P ⊆ S ∧ (∀ p ∈ S, p.2 ∈ _root_.Set.Icc a b) ∧
      (∀ r ∈ _root_.Set.Icc a b, ∀ q : UniformSpace.Completion (Quotient K.setoid),
        ∃ p ∈ S, Metric.coneDistance (r, q)
          (p.2, (K.classOf p.1 : UniformSpace.Completion (Quotient K.setoid))) < eps) ∧
      ∀ᶠ rho in 𝓝[>] (0 : ℝ),
        (∀ p ∈ S, rho * p.2 ∈ _root_.Set.Ioc 0 (L p.1)) ∧
        (∀ i, ∀ r ∈ _root_.Set.Icc a b, rho * r ≤ L i →
          ∃ p ∈ S, _root_.Dist.dist (gamma i (rho * r)) (gamma p.1 (rho * p.2)) / rho < eps) ∧
        (∀ p ∈ S, _root_.Dist.dist z (gamma p.1 (rho * p.2)) / rho = p.2) ∧
        ∀ p ∈ S, ∀ q ∈ S,
          |Metric.coneDistance (p.2, (K.classOf p.1 : UniformSpace.Completion (Quotient K.setoid)))
            (q.2, (K.classOf q.1 : UniformSpace.Completion (Quotient K.setoid))) -
            dist (gamma p.1 (rho * p.2)) (gamma q.1 (rho * q.2)) / rho| < eps := by
  classical
  let _ := K.metricSpace
  change ∃ S : Finset (ι × ℝ), _
  obtain ⟨S0, hS0, hcone, d, hd, hlen, hcover⟩ :=
    exists_finset_radial_annulus_net hrad hL hmin K hK htb ha hab heps
  let S := S0 ∪ P
  have hS (p : ι × ℝ) (hp : p ∈ S) : p.2 ∈ _root_.Set.Icc a b := by
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hS0 p hp
    · exact hP p hp
  have hdomain (p : ι × ℝ) (hp : p ∈ S) : ∀ᶠ rho in 𝓝[>] (0 : ℝ),
      rho * p.2 ∈ _root_.Set.Ioc 0 (L p.1) := by
    have hp0 : 0 < p.2 := ha.trans_le (hS p hp).1
    filter_upwards [Ioc_mem_nhdsGT (div_pos (hL p.1) hp0)] with rho hrho
    exact ⟨mul_pos hrho.1 hp0, (le_div_iff₀ hp0).mp hrho.2⟩
  have hpair (p : ι × ℝ) (hp : p ∈ S) (q : ι × ℝ) (hq : q ∈ S) :
      ∀ᶠ rho in 𝓝[>] (0 : ℝ),
        |Metric.coneDistance (p.2, (K.classOf p.1 : UniformSpace.Completion (Quotient K.setoid)))
          (q.2, (K.classOf q.1 : UniformSpace.Completion (Quotient K.setoid))) -
          dist (gamma p.1 (rho * p.2)) (gamma q.1 (rho * q.2)) / rho| < eps := by
    have hlim := tendsto_rescaled_radial_distance hrad (hL p.1) (hL q.1) (hmono p.1 q.1)
      (ha.trans_le (hS p hp).1) (ha.trans_le (hS q hq).1)
    have hdist : _root_.Dist.dist (K.classOf p.1 : UniformSpace.Completion (Quotient K.setoid))
        (K.classOf q.1 : UniformSpace.Completion (Quotient K.setoid)) =
        limitingRadialAngle L gamma p.1 q.1 := by
      rw [UniformSpace.Completion.dist_eq]
      exact hK p.1 q.1
    have htheta := (limitingRadialAngle_mem_Icc gamma (hL p.1) (hL q.1)).2
    have hlim' : _root_.Filter.Tendsto (fun rho : ℝ => _root_.Dist.dist (gamma p.1 (rho * p.2))
        (gamma q.1 (rho * q.2)) / rho) (𝓝[>] (0 : ℝ))
        (𝓝 (Metric.coneDistance (p.2, (K.classOf p.1 : UniformSpace.Completion (Quotient K.setoid)))
          (q.2, (K.classOf q.1 : UniformSpace.Completion (Quotient K.setoid))))) := by
      simpa only [Metric.coneDistance, hdist, min_eq_right htheta] using hlim
    simpa only [Real.dist_eq, abs_sub_comm] using (Metric.tendsto_nhds.mp hlim') eps heps
  have hdomains := (_root_.Filter.eventually_all_finset S).mpr hdomain
  have hpairs := (_root_.Filter.eventually_all_finset S).mpr
    (fun p hp => (_root_.Filter.eventually_all_finset S).mpr (hpair p hp))
  refine ⟨S, Finset.subset_union_right, hS, ?_, ?_⟩
  · intro r hr q
    obtain ⟨p, hp, hnear⟩ := hcone r hr q
    exact ⟨p, Finset.mem_union_left P hp, hnear⟩
  · filter_upwards [Ioc_mem_nhdsGT hd, hdomains, hpairs] with rho hrho hdom hpair
    refine ⟨hdom, ?_, ?_, hpair⟩
    · intro i r hr hri
      obtain ⟨p, hp, hnear⟩ := hcover rho hrho i r hr hri
      exact ⟨p, Finset.mem_union_left P hp, hnear⟩
    · intro p hp
      rw [hrad p.1 (rho * p.2) (hdom p hp), mul_div_cancel_left₀ _ hrho.1.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Toponogov.exists_finset_radial_cone_approximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Toponogov.exists_finset_radial_cone_approximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Toponogov.exists_finset_radial_cone_approximation ``Submission.DifferentialGeometry.Toponogov.exists_finset_radial_cone_approximation


end DifferentialGeometry.Toponogov
