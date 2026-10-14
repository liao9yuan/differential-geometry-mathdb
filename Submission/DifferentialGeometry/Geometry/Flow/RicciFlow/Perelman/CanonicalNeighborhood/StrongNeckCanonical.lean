import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckCapCompactDomains
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.GoodPointDerivatives
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open _root_.Submission.DifferentialGeometry.Integral.Measure _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {x : M} {t : ℝ} {U : Set M}

theorem StrongNeck.exists_canonicalWitness_of_scalar_pos
    {eps : ℝ} (nk : StrongNeck S eps x t)
    (hpositive : ∀ y ∈ nk.region, 0 < S.scalar t y) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ K : CanonicalWitness S eps 9 C x t,
      K.domain.carrier = nk.region ∧ K.radius = 9 / Real.sqrt (S.scalar t x) ∧
      ∃ data : LocalNeck S eps x t K.domain.carrier,
        K.alternative = CanonicalAlternative.neck data ∧ data.strong = nk := by
  obtain ⟨domain, hdomain, hxDomain⟩ := nk.exists_compactDomain_region
  have hxU : x ∈ interior nk.region := hdomain ▸ hxDomain
  have hcompact : IsCompact nk.region := hdomain ▸ domain.compact
  let U := nk.region
  let : IsManifold I3 1 M := IsManifold.of_le (n := ∞) (by decide)
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hx : x ∈ U := interior_subset hxU
  have hUne : U.Nonempty := ⟨x, hx⟩
  have hcont : Continuous (S.scalar t) := (metricScalar_smooth (S.base.metric t)).continuous
  obtain ⟨ymin, hymin, hmin⟩ := hcompact.exists_isMinOn hUne hcont.continuousOn
  obtain ⟨ymax, _, hmax⟩ := hcompact.exists_isMaxOn hUne hcont.continuousOn
  let m := S.scalar t ymin
  let B := S.scalar t ymax
  have hm : 0 < m := hpositive ymin hymin
  let Q := S.scalar t x
  have hQ : 0 < Q := hpositive x hx
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  let curvature : M → ℝ := fun y => Real.sqrt (FlowMetricBall.rmNormSq S t y)
  have hcurvature : Continuous curvature := by
    exact Real.continuous_sqrt.comp
      (DifferentialGeometry.Tensor.RSTensor.normSq0S_smooth
        (S.base.metric t) (metricRm04 (S.base.metric t))).continuous
  obtain ⟨zmax, _, hcurv⟩ := hcompact.exists_isMaxOn hUne hcurvature.continuousOn
  let Bcurv := curvature zmax
  let G := (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 *
    Real.sqrt (nablaKRm04NormSqIntrinsic (I := I3) S 1 t x)
  let T := |derivWithin (fun s => S.scalar s x) (_root_.Set.Iic t) t|
  let mu := riemannianVolumeMeasure I3 M (S.base.metric t)
  let : _root_.MeasureTheory.IsLocallyFiniteMeasure mu :=
    riemannianVolumeMeasure_isLocallyFiniteMeasure (S.base.metric t)
  let : mu.IsOpenPosMeasure := riemannianVolumeMeasure_isOpenPosMeasure (S.base.metric t)
  have hvol : 0 < mu U :=
    (isOpen_interior.measure_pos mu ⟨x, hxU⟩).trans_le (_root_.MeasureTheory.measure_mono interior_subset)
  have hvfin : mu U ≠ ⊤ := hcompact.measure_lt_top.ne
  let V := (mu U).toReal
  have hV : 0 < V := ENNReal.toReal_pos hvol.ne' hvfin
  obtain ⟨C, hC⟩ := _root_.NoMaxOrder.exists_gt (_root_.Max.max 1 (_root_.Max.max (Q / m) (_root_.Max.max (B / Q) (_root_.Max.max (Bcurv / Q)
    (_root_.Max.max (G / (Q * Real.sqrt Q)) (_root_.Max.max (T / Q ^ 2) (V * (Q * Real.sqrt Q))⁻¹))))))
  have hCs : 1 < C ∧ Q / m < C ∧ B / Q < C ∧ Bcurv / Q < C ∧
      G / (Q * Real.sqrt Q) < C ∧ T / Q ^ 2 < C ∧
      (V * (Q * Real.sqrt Q))⁻¹ < C := by simpa only [max_lt_iff] using hC
  obtain ⟨hC1, hCm, hCB, hCrm, hCG, hCT, hCV⟩ := hCs
  have hCp : 0 < C := zero_lt_one.trans hC1
  have hCmin : C⁻¹ * Q ≤ m := by
    rw [← div_eq_inv_mul, div_le_iff₀ hCp]
    simpa only [mul_comm] using (div_le_iff₀ hm).mp hCm.le
  have hCvol : C⁻¹ / (Q * Real.sqrt Q) ≤ V := by
    rw [div_le_iff₀ (mul_pos hQ hroot)]
    exact (inv_le_comm₀ hCp (mul_pos hV (mul_pos hQ hroot))).mpr hCV.le
  have hbound : 9 ≤ 10 * Real.sqrt (1 - eps) := by
    have hroot : (9 / 10 : ℝ) ≤ Real.sqrt (1 - eps) := by
      apply Real.le_sqrt_of_sq_le
      linarith [nk.eps_small]
    linarith
  have hinner : riemannianBallOf (S.base.metric t) x (9 / Real.sqrt Q) ⊆ nk.region :=
    (riemannianBallOf_mono _ _ (div_le_div_of_nonneg_right hbound hroot.le)).trans nk.ball_subset_region
  have houter : nk.region ⊆ riemannianBallOf (S.base.metric t) x (2 * (9 / Real.sqrt Q)) :=
    nk.region_subset_ball.trans (riemannianBallOf_mono _ _ (by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (by norm_num) hroot.le))
  let data : LocalNeck S eps x t domain.carrier := {
    strong := nk
    region_eq := hdomain
    boundary_eq := by
      rw [hdomain, nk.frontier_region_eq_union_boundary_spheres, ← _root_.Set.image_union, ← _root_.Set.prod_union]
      rfl }
  let K : CanonicalWitness S eps 9 C x t := {
    Q_pos := hQ
    time_mem := nk.time_domain ⟨by linarith [inv_pos.mpr nk.Q_pos], le_rfl⟩
    eps_pos := nk.eps_pos
    eps_lt_one := nk.eps_small.trans (by norm_num)
    domain := domain
    center_inside := hxDomain
    radius := 9 / Real.sqrt Q
    radius_lower := by rw [← one_div]; exact div_le_div_of_nonneg_right (by norm_num) hroot.le
    radius_upper := le_rfl
    ball_inside := by rw [hdomain]; exact hinner
    inside_ball := by rw [hdomain]; exact houter
    scalar_bounds := fun y hy => ⟨hCmin.trans (hmin (hdomain ▸ hy)),
      (hmax (hdomain ▸ hy)).trans ((div_le_iff₀ hQ).mp hCB.le)⟩
    rm_bound := fun y hy => (hcurv (hdomain ▸ hy)).trans ((div_le_iff₀ hQ).mp hCrm.le)
    alternative := CanonicalAlternative.neck data
    volume := by
      intro _
      change ENNReal.ofReal (C⁻¹ / (Q * Real.sqrt Q)) ≤ mu domain.carrier
      rw [hdomain]
      exact (ENNReal.ofReal_le_ofReal hCvol).trans (by rw [ENNReal.ofReal_toReal hvfin])
    gradient := by
      intro v
      have h := abs_scalarDifferential_le S t x v
      have hGQ : G ≤ C * Q * Real.sqrt Q := by
        simpa only [mul_assoc] using (div_le_iff₀ (mul_pos hQ hroot)).mp hCG.le
      exact h.trans (mul_le_mul_of_nonneg_right hGQ (Real.sqrt_nonneg _))
    time_derivative := (div_le_iff₀ (sq_pos_of_pos hQ)).mp hCT.le }
  exact ⟨C, hC1.le, K, hdomain, rfl, data, rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.exists_canonicalWitness_of_scalar_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.exists_canonicalWitness_of_scalar_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.exists_canonicalWitness_of_scalar_pos ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.StrongNeck.exists_canonicalWitness_of_scalar_pos

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
