import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveComponentModels
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BufferedCanonical
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  [CompactSpace M] [ConnectedSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {x : M} {t : ℝ}

theorem exists_positive_canonicalWitness_of_compact
    (ht : t ∈ D.carrier) (hpositive : ∀ y : M, 0 < S.scalar t y)
    (data : PositiveComponent (_root_.Set.univ : Set M)) {sec : ℝ} (hsec : 0 < sec)
    (hsectional : SecLower (S.base.metric t) sec _root_.Set.univ) :
    ∃ A C : ℝ, 1 ≤ A ∧ 1 ≤ C ∧ ∀ eps : ℝ, 0 < eps → eps < 1 →
      ∃ K : CanonicalWitness S eps A C x t, K.domain.carrier = _root_.Set.univ ∧
        ∃ whole positive lower, K.alternative = CanonicalAlternative.positive whole positive lower := by
  let _ : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hcont : Continuous (S.scalar t) := (metricScalar_smooth (S.base.metric t)).continuous
  obtain ⟨ymin, _hymin, hmin⟩ := isCompact_univ.exists_isMinOn (_root_.Set.univ_nonempty : (_root_.Set.univ : Set M).Nonempty) hcont.continuousOn
  obtain ⟨ymax, _hymax, hmax⟩ := isCompact_univ.exists_isMaxOn (_root_.Set.univ_nonempty : (_root_.Set.univ : Set M).Nonempty) hcont.continuousOn
  let m := S.scalar t ymin
  let B := S.scalar t ymax
  have hm : 0 < m := hpositive ymin
  let Q := S.scalar t x
  have hQ : 0 < Q := hpositive x
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  let curvature : M → ℝ := fun y => Real.sqrt (FlowMetricBall.rmNormSq S t y)
  have hcurvature : Continuous curvature := Real.continuous_sqrt.comp
    (DifferentialGeometry.Tensor.RSTensor.normSq0S_smooth (S.base.metric t) (metricRm04 (S.base.metric t))).continuous
  obtain ⟨zmax, _hzmax, hcurv⟩ := isCompact_univ.exists_isMaxOn
    (_root_.Set.univ_nonempty : (_root_.Set.univ : Set M).Nonempty) hcurvature.continuousOn
  let Bcurv := curvature zmax
  let G := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 * Real.sqrt (nablaKRm04NormSqIntrinsic S 1 t x)
  let T := |derivWithin (fun s => S.scalar s x) (_root_.Set.Iic t) t|
  let mu := riemannianVolumeMeasure I3 M (S.base.metric t)
  let _ : _root_.MeasureTheory.IsLocallyFiniteMeasure mu := riemannianVolumeMeasure_isLocallyFiniteMeasure (S.base.metric t)
  let _ : mu.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure (S.base.metric t)
  have hvol : 0 < mu univ := isOpen_univ.measure_pos mu _root_.Set.univ_nonempty
  have hvfin : mu _root_.Set.univ ≠ ⊤ := isCompact_univ.measure_lt_top.ne
  let V := (mu _root_.Set.univ).toReal
  have hV : 0 < V := ENNReal.toReal_pos hvol.ne' hvfin
  have hdist : Continuous (fun y => metricDistance (S.base.metric t) x y) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (ENNReal.continuousAt_toReal (riemannianEDistOf_ne_top (S.base.metric t) x y)).comp
      (continuous_riemannianEDist (S.base.metric t) x).continuousAt
  obtain ⟨yfar, _hyfar, hfar⟩ := isCompact_univ.exists_isMaxOn
    (_root_.Set.univ_nonempty : (_root_.Set.univ : Set M).Nonempty) hdist.continuousOn
  let r := _root_.Max.max (Real.sqrt Q)⁻¹ (metricDistance (S.base.metric t) x yfar + 1)
  have hr : (Real.sqrt Q)⁻¹ ≤ r := le_max_left _ _
  have hrpos : 0 < r := (inv_pos.mpr hroot).trans_le hr
  have hAr : 1 ≤ r * Real.sqrt Q := by
    have hh := mul_le_mul_of_nonneg_right hr hroot.le
    simpa only [inv_mul_cancel₀ hroot.ne'] using hh
  have houter : (_root_.Set.univ : Set M) ⊆ riemannianBallOf (S.base.metric t) x (2 * r) := by
    intro y _
    have hy : metricDistance (S.base.metric t) x y < 2 * r := by
      have hh : metricDistance (S.base.metric t) x y ≤ metricDistance (S.base.metric t) x yfar := hfar (_root_.Set.mem_univ y)
      have hh' := le_max_right (Real.sqrt Q)⁻¹ (metricDistance (S.base.metric t) x yfar + 1)
      change metricDistance (S.base.metric t) x yfar + 1 ≤ r at hh'
      linarith
    change riemannianEDistOf (S.base.metric t) x y < ENNReal.ofReal (2 * r)
    rw [← ENNReal.ofReal_toReal (riemannianEDistOf_ne_top (S.base.metric t) x y)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < 2 * r)).mpr hy
  obtain ⟨C, hC⟩ := _root_.NoMaxOrder.exists_gt (_root_.Max.max 1 (_root_.Max.max (Q / m) (_root_.Max.max (B / Q) (_root_.Max.max (Bcurv / Q)
    (_root_.Max.max (G / (Q * Real.sqrt Q)) (_root_.Max.max (T / Q ^ 2) (_root_.Max.max (V * (Q * Real.sqrt Q))⁻¹ (Q / sec))))))))
  have hCs : 1 < C ∧ Q / m < C ∧ B / Q < C ∧ Bcurv / Q < C ∧
      G / (Q * Real.sqrt Q) < C ∧ T / Q ^ 2 < C ∧ (V * (Q * Real.sqrt Q))⁻¹ < C ∧ Q / sec < C := by
    simpa only [max_lt_iff] using hC
  obtain ⟨hC1, hCm, hCB, hCrm, hCG, hCT, hCV, hCsec⟩ := hCs
  have hCp : 0 < C := zero_lt_one.trans hC1
  have hCmin : C⁻¹ * Q ≤ m := by
    rw [← div_eq_inv_mul, div_le_iff₀ hCp]
    simpa only [mul_comm] using (div_le_iff₀ hm).mp hCm.le
  have hCvol : C⁻¹ / (Q * Real.sqrt Q) ≤ V := by
    rw [div_le_iff₀ (mul_pos hQ hroot)]
    exact (inv_le_comm₀ hCp (mul_pos hV (mul_pos hQ hroot))).mpr hCV.le
  have hCsec' : C⁻¹ * Q ≤ sec := by
    rw [← div_eq_inv_mul, div_le_iff₀ hCp]
    simpa only [mul_comm] using (div_le_iff₀ hsec).mp hCsec.le
  let domain : CompactDomain M := {
    carrier := _root_.Set.univ
    compact := isCompact_univ
    connected := isConnected_univ
    regular_closed := by simp
    boundary_chart := by simp }
  refine ⟨r * Real.sqrt Q, C, hAr, hC1.le, ?_⟩
  intro eps heps heps1
  have whole : domain.carrier = connectedComponent x := (PreconnectedSpace.connectedComponent_eq_univ (x := x)).symm
  have lower : SecLower (S.base.metric t) (C⁻¹ * Q) domain.carrier := hsectional.mono hCsec'
  let K : CanonicalWitness S eps (r * Real.sqrt Q) C x t := {
    Q_pos := hQ
    time_mem := ht
    eps_pos := heps
    eps_lt_one := heps1
    domain := domain
    center_inside := by change x ∈ interior (_root_.Set.univ : Set M); rw [interior_univ]; trivial
    radius := r
    radius_lower := hr
    radius_upper := by rw [mul_div_cancel_right₀ _ hroot.ne']
    ball_inside := _root_.Set.subset_univ _
    inside_ball := houter
    scalar_bounds := fun y _ => ⟨hCmin.trans (hmin (_root_.Set.mem_univ y)),
      (hmax (_root_.Set.mem_univ y)).trans ((div_le_iff₀ hQ).mp hCB.le)⟩
    rm_bound := fun y _ => (hcurv (_root_.Set.mem_univ y)).trans ((div_le_iff₀ hQ).mp hCrm.le)
    alternative := CanonicalAlternative.positive whole data lower
    volume := by
      intro _
      exact (ENNReal.ofReal_le_ofReal hCvol).trans (by rw [ENNReal.ofReal_toReal hvfin])
    gradient := by
      intro v
      have h := abs_scalarDifferential_le S t x v
      have hGQ : G ≤ C * Q * Real.sqrt Q := by
        simpa only [mul_assoc] using (div_le_iff₀ (mul_pos hQ hroot)).mp hCG.le
      exact h.trans (mul_le_mul_of_nonneg_right hGQ (Real.sqrt_nonneg _))
    time_derivative := (div_le_iff₀ (sq_pos_of_pos hQ)).mp hCT.le }
  exact ⟨K, rfl, whole, data, lower, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_positive_canonicalWitness_of_compact then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_positive_canonicalWitness_of_compact"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_positive_canonicalWitness_of_compact ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_positive_canonicalWitness_of_compact

theorem exists_bufferedCanonical_of_compact_positive
    (ht : t ∈ D.carrier) (hpositive : ∀ y : M, 0 < S.scalar t y)
    (data : PositiveComponent (_root_.Set.univ : Set M)) {sec : ℝ} (hsec : 0 < sec)
    (hsectional : SecLower (S.base.metric t) sec _root_.Set.univ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ alpha : ℝ, 0 < alpha → ∀ H : ℝ,
      Nonempty (BufferedCanonical S alpha C H x t) := by
  obtain ⟨A, C, hA, hC, hK⟩ := exists_positive_canonicalWitness_of_compact (x := x)
    ht hpositive data hsec hsectional
  refine ⟨max A C + 1, by linarith [le_max_right A C], ?_⟩
  intro alpha ha H
  let eps := _root_.Min.min (alpha / 2) (1 / 2 : ℝ)
  have heps : 0 < eps := lt_min (by positivity) (by norm_num)
  have heps1 : eps < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hepsa : eps < alpha := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨K, _hKuniv, whole, positive, lower, hKalt⟩ := hK eps heps heps1
  apply K.exists_bufferedCanonical hepsa
  intro cap hc
  obtain ⟨depth, halt⟩ := hc
  rw [hKalt] at halt
  cases halt

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_bufferedCanonical_of_compact_positive then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_bufferedCanonical_of_compact_positive"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_bufferedCanonical_of_compact_positive ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_bufferedCanonical_of_compact_positive

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
