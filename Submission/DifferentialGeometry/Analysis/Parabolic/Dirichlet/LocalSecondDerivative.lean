import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletLocalSecondDerivative
import Submission.DifferentialGeometry.Analysis.Sobolev.Chart.ChartDensityCutoff
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Density
import Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.LocalNirenbergInteriorTime

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.NNReal _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

theorem exists_local_dirichlet_second_weak_derivative_of_timeH1
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a ≤ b) (hreg : _root_.Set.Icc a b ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1)
    {η : EuStd → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω) (hηb : ∀ z, |η z| ≤ 1)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ t ∈ _root_.Set.Icc a b, ∀ y ∈ Ω, ∀ ξ : Fin (Module.finrank ℝ EuN) → ℝ,
      lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, invGramOnEuclid (G.metric t) α i j y * ξ i * ξ j)
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 (volume.restrict (_root_.Set.Icc a b)))
    (f : _root_.MeasureTheory.Lp ℝ 2 ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)))
    (ℓ β : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 (volume.restrict (_root_.Set.Icc a b)))
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a))
    (hwmass : ∀ᵐ s ∂timeMeasure (b - a), ∀ z,
      w.toFun s z = _root_.Inner.inner ℝ (H1ComplDirichletToLp q (v (a + s))) (H1ComplDirichletToLp q z))
    (hwderiv : w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s))
    (hpair : ∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 (volume.restrict (_root_.Set.Icc a b)),
      (∫ t in _root_.Set.Icc a b, ℓ t (z t)) = (∫ t in _root_.Set.Icc a b, β t (z t)) -
        ∫ t in _root_.Set.Icc a b, (∑ i, ∑ j, ∫ y in Ω,
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) y *
            (densityOnEuclid q α y * invGramOnEuclid (G.metric t) α i j y) *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (z t) y))
    (hsource : ∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 (volume.restrict (_root_.Set.Icc a b)),
      (∫ t in _root_.Set.Icc a b, β t (z t)) = ∫ t in _root_.Set.Icc a b, (∫ y in Ω,
        f (t,y) * H1ComplDirichletToLp q (z t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm y))))
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hηone : ∀ z ∈ Ω₀, η z = 1) :
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        _root_.MeasureTheory.Lp ℝ 2 (((volume.restrict (_root_.Set.Icc a b)).restrict (_root_.Set.Icc c d)).prod (volume.restrict Ω₀)),
      (∀ i k, ∀ᵐ t ∂(volume.restrict (_root_.Set.Icc a b)).restrict (_root_.Set.Icc c d),
        DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) Ω₀) ∧
      ∀ᵐ t ∂(volume.restrict (_root_.Set.Icc a b)).restrict (_root_.Set.Icc c d),
        Sobolev.Euclidean.MemWkp 2 2
          (fun z => H1ComplDirichletToLp q (v t)
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀ := by
  obtain ⟨δ, hδ, C, _, hroom, hbound⟩ :=
    exists_local_dirichlet_nirenberg_integral_Icc_bound hG hab hreg q α hΩ hΩc hΩs
      φ hφ hη hηc hηs hηb hlam hcoer hac hdb
  exact DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_lp_second_weak_derivative_of_local_diffQuot_bound_restrict q α hΩ hΩc hΩs
    (_root_.Set.Icc c d) v (hη.of_le (by simp)) hηc hΩ₀ hηone hδ hroom
    (fun k h _ hh => hbound v f ℓ β w hwmass hwderiv hpair hsource k h hh)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_local_dirichlet_second_weak_derivative_of_timeH1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_local_dirichlet_second_weak_derivative_of_timeH1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_local_dirichlet_second_weak_derivative_of_timeH1 ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_local_dirichlet_second_weak_derivative_of_timeH1


omit [T2Space M] [CompactSpace M] in
private theorem exists_uniform_inv_gram_sum_lower_bound
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {J : Set ℝ} (hJc : IsCompact J) (hJ : J ⊆ D.regular) (α : M)
    {K : Set EuStd} (hKc : IsCompact K)
    (hKs : K ⊆ chartTargetEuclid (I := I_hs) α) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ t ∈ J, ∀ y ∈ K,
      ∀ ξ : Fin (Module.finrank ℝ EuN) → ℝ,
        lam * ∑ i, (ξ i)^2 ≤ ∑ i, ∑ j, invGramOnEuclid (G.metric t) α i j y * ξ i * ξ j := by
  obtain ⟨lam, hlam, hcoer⟩ := exists_uniform_inv_gram_quadratic_lower_bound hG hJc hJ α hKc hKs
  refine ⟨lam, hlam, ?_⟩
  intro t ht y hy ξ
  have hb := hcoer t ht y hy (WithLp.toLp 2 ξ)
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs,
    PiLp.inner_apply, DeGiorgi.matMulE_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Real.inner_apply] at hb
  convert hb using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_uniform_inv_gram_sum_lower_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_uniform_inv_gram_sum_lower_bound target :: scope.openDecls } }

theorem exists_local_dirichlet_second_weak_derivative_of_timeH1_interior
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a ≤ b) (hreg : _root_.Set.Icc a b ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 (volume.restrict (_root_.Set.Icc a b)))
    (f : _root_.MeasureTheory.Lp ℝ 2 ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)))
    (ℓ β : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 (volume.restrict (_root_.Set.Icc a b)))
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a))
    (hwmass : ∀ᵐ s ∂timeMeasure (b - a), ∀ z,
      w.toFun s z = _root_.Inner.inner ℝ (H1ComplDirichletToLp q (v (a + s))) (H1ComplDirichletToLp q z))
    (hwderiv : w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s))
    (hpair : ∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 (volume.restrict (_root_.Set.Icc a b)),
      (∫ t in _root_.Set.Icc a b, ℓ t (z t)) = (∫ t in _root_.Set.Icc a b, β t (z t)) -
        ∫ t in _root_.Set.Icc a b, (∑ i, ∑ j, ∫ y in Ω,
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) y *
            (densityOnEuclid q α y * invGramOnEuclid (G.metric t) α i j y) *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (z t) y))
    (hsource : ∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 (volume.restrict (_root_.Set.Icc a b)),
      (∫ t in _root_.Set.Icc a b, β t (z t)) = ∫ t in _root_.Set.Icc a b, (∫ y in Ω,
        f (t,y) * H1ComplDirichletToLp q (z t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm y))))
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        _root_.MeasureTheory.Lp ℝ 2 (((volume.restrict (_root_.Set.Icc a b)).restrict (_root_.Set.Icc c d)).prod (volume.restrict Ω₀)),
      (∀ i k, ∀ᵐ t ∂(volume.restrict (_root_.Set.Icc a b)).restrict (_root_.Set.Icc c d),
        DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) Ω₀) ∧
      ∀ᵐ t ∂(volume.restrict (_root_.Set.Icc a b)).restrict (_root_.Set.Icc c d),
        Sobolev.Euclidean.MemWkp 2 2
          (fun z => H1ComplDirichletToLp q (v t)
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀ := by
  have hΩ₀c : IsCompact (closure Ω₀) :=
    hΩc.of_isClosed_subset isClosed_closure (hΩ₀Ω.trans subset_closure)
  obtain ⟨δ, η, _, _, hη, hηc, hηrange, hηone, hηs⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_smooth_cutoff_with_neighborhood
      hΩ₀c hΩ hΩ₀Ω
  have hηb : ∀ z, |η z| ≤ 1 := by
    intro z
    have hz := hηrange (_root_.Set.mem_range_self z)
    exact (abs_le.mpr ⟨by linarith [hz.1], hz.2⟩)
  let U := toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target
  have hU : IsOpen U := (toEuclidean (E := EuN)).isOpenMap _ isOpen_interior
  obtain ⟨φ, _, hφ0⟩ := DifferentialGeometry.Analysis.Sobolev.Chart.exists_smoothMap_mul_chartDensity_eq_one
    q α hU (Subset.rfl : U ⊆ U) hΩc hΩs
  have hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)) = 1 := by
    intro z hz
    exact hφ0 z (subset_closure hz)
  obtain ⟨lam, hlam, hcoer⟩ := exists_uniform_inv_gram_sum_lower_bound
    hG _root_.CompactIccSpace.isCompact_Icc hreg α hΩc (hΩs.trans (_root_.Set.image_mono interior_subset))
  exact exists_local_dirichlet_second_weak_derivative_of_timeH1
    hG hab hreg q α hΩ hΩc hΩs φ hφ hη hηc hηs hηb hlam (fun t ht y hy => hcoer t ht y (subset_closure hy)) hac hdb
    v f ℓ β w hwmass hwderiv hpair hsource hΩ₀
    (fun z hz => hηone z (Metric.self_subset_cthickening (closure Ω₀) (subset_closure hz)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_local_dirichlet_second_weak_derivative_of_timeH1_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_local_dirichlet_second_weak_derivative_of_timeH1_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_local_dirichlet_second_weak_derivative_of_timeH1_interior ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_local_dirichlet_second_weak_derivative_of_timeH1_interior

theorem exists_local_dirichlet_second_weak_derivative_of_timeH1_of_measure_eq_volume
    {D : RealTimeInterval} {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric)
    {a b : ℝ} (hab : a ≤ b) (hreg : _root_.Set.Icc a b ⊆ D.regular)
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    {c d : ℝ} (hac : a < c) (hdb : d < b)
    {μ : _root_.MeasureTheory.Measure ℝ} (hμ : μ = volume.restrict (_root_.Set.Icc a b))
    (v : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ)
    (f : _root_.MeasureTheory.Lp ℝ 2 (μ.prod (volume.restrict Ω)))
    (ℓ β : _root_.MeasureTheory.Lp (H1ComplDirichlet q →L[ℝ] ℝ) 2 μ)
    (w : timeH1 (H1ComplDirichlet q →L[ℝ] ℝ) (b - a))
    (hwmass : ∀ᵐ s ∂timeMeasure (b - a), ∀ z,
      w.toFun s z = _root_.Inner.inner ℝ (H1ComplDirichletToLp q (v (a + s)))
        (H1ComplDirichletToLp q z))
    (hwderiv : w.deriv =ᵐ[timeMeasure (b - a)] fun s => ℓ (a + s))
    (hpair : ∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ,
      (∫ t, ℓ t (z t) ∂μ) = (∫ t, β t (z t) ∂μ) -
        ∫ t, (∑ i, ∑ j, ∫ y in Ω,
          dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t) y *
            (densityOnEuclid q α y * invGramOnEuclid (G.metric t) α i j y) *
            dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (z t) y) ∂μ)
    (hsource : ∀ z : _root_.MeasureTheory.Lp (H1ComplDirichlet q) 2 μ,
      (∫ t, β t (z t) ∂μ) = ∫ t, (∫ y in Ω,
        f (t, y) * H1ComplDirichletToLp q (z t)
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm y))) ∂μ)
    {Ω₀ : Set EuStd} (hΩ₀ : IsOpen Ω₀) (hΩ₀Ω : closure Ω₀ ⊆ Ω) :
    ∃ H : Fin (Module.finrank ℝ EuN) → Fin (Module.finrank ℝ EuN) →
        _root_.MeasureTheory.Lp ℝ 2 (((volume.restrict (_root_.Set.Icc a b)).restrict (_root_.Set.Icc c d)).prod
          (volume.restrict Ω₀)),
      (∀ i k, ∀ᵐ t ∂(volume.restrict (_root_.Set.Icc a b)).restrict (_root_.Set.Icc c d),
        DeGiorgi.HasWeakPartialDeriv k (fun z => H i k (t, z))
          (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (v t)) Ω₀) ∧
      ∀ᵐ t ∂(volume.restrict (_root_.Set.Icc a b)).restrict (_root_.Set.Icc c d),
        Sobolev.Euclidean.MemWkp 2 2
          (fun z => H1ComplDirichletToLp q (v t)
            ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))) Ω₀ := by
  cases hμ
  exact exists_local_dirichlet_second_weak_derivative_of_timeH1_interior
    hG hab hreg q α hΩ hΩc hΩs hac hdb v f ℓ β w hwmass hwderiv hpair hsource
      hΩ₀ hΩ₀Ω

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_local_dirichlet_second_weak_derivative_of_timeH1_of_measure_eq_volume then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_local_dirichlet_second_weak_derivative_of_timeH1_of_measure_eq_volume"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_local_dirichlet_second_weak_derivative_of_timeH1_of_measure_eq_volume ``Submission.DifferentialGeometry.Analysis.Parabolic.Dirichlet.exists_local_dirichlet_second_weak_derivative_of_timeH1_of_measure_eq_volume

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
