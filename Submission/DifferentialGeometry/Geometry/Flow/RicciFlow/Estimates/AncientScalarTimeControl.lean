import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.CompleteGlobal
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarLaplacian
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.IntrinsicDerivation
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import Mathlib.Analysis.Calculus.MeanValue

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Set
open _root_.Submission.DifferentialGeometry.Geometry.Curvature _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}

private local instance scalarTimeControlC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarTimeControlC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.scalarTimeControlC1 target :: scope.openDecls } }
private local instance scalarTimeControlC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.scalarTimeControlC2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.scalarTimeControlC2 target :: scope.openDecls } }

theorem exists_scalar_derivative_bound_of_complete_ancient_bounded_curvature
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b K : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b)
    (hK : 0 < K)
    (hcomplete : ∀ t ≤ b, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ t ≤ b, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t < b, ∀ x : M,
      |deriv (fun s : ℝ => S.scalar s x) t| ≤ C := by
  let d : ℝ := Module.finrank ℝ E
  let B : ℝ := shiCompleteGlobalBound (Module.finrank ℝ E) 2 * K * (1 + Real.sqrt K) ^ 2
  have hB : 0 ≤ B := by
    exact mul_nonneg (mul_nonneg (shiCompleteGlobalBound_nonneg _ _) hK.le) (sq_nonneg _)
  refine ⟨d ^ 6 * B + 2 * d ^ 4 * K ^ 2, by positivity, ?_⟩
  intro t ht x
  let W := RealTimeInterval.closedOpen (t - 2) b (by linarith : t - 2 < b)
  let S' := S.timeRestrict W
  have hS' : IsSolutionOn S' := isSolutionOn_timeRestrict hS
    (by intro s hs; rw [hcarrier]; exact hs.2.le)
    (by intro s hs; rw [hregular]; exact hs.2)
  have hcurv' : ∀ s ∈ _root_.Set.Icc (t - 1) t, ∀ y : M,
      nablaKRm04NormSqIntrinsic S' 0 s y ≤ K ^ 2 := by
    intro s hs y
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero,
      S', SolutionOn.timeRestrict] using
      hcurv s (hs.2.trans ht.le) y
  have hsecond : Real.sqrt (nablaKRm04NormSqIntrinsic S 2 t x) ≤ B := by
    have h := shi_positive_slab_of_solution S' hS' (a₀ := t - 1) (a := t) (b := t)
      (by linarith) (by linarith) ht hK (hcomplete (t - 1) (by linarith)) hcurv'
      2 t ⟨le_rfl, le_rfl⟩ x
    have hdifference : t - (t - 1) = 1 := by ring
    have hrestrict : nablaKRm04NormSqIntrinsic S' 2 t x =
        nablaKRm04NormSqIntrinsic S 2 t x := rfl
    rw [hrestrict, hdifference, Real.sqrt_one, div_one] at h
    exact h
  have hlap := Perelman.CanonicalNeighborhood.abs_laplacian_scalar_le_second_curvature S t x
  have hlap' : |laplacianAt (flowG S) t (S.scalar t) x| ≤ d ^ 6 * B :=
    hlap.trans (mul_le_mul_of_nonneg_left hsecond (by positivity))
  have hric := ricTower_normSq_le (I := I) S t 0 x
  have hzero : nablaKRm04NormSqIntrinsic S 0 t x ≤ K ^ 2 := by
    simpa only [nablaKRm04NormSqIntrinsic, nablaKRm04Field_zero, Nat.add_zero] using
      hcurv t ht.le x
  have hric' : normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x) ≤ d ^ 4 * K ^ 2 :=
    hric.trans (mul_le_mul_of_nonneg_left hzero (by positivity))
  have hric0 : 0 ≤ normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x) :=
    normSq0S_nonneg _ _ _ _
  have htreg : t ∈ D.regular := by rwa [hregular]
  have hevol := scalar_curvature_evolution S hS ⟨t, htreg⟩ x
  rw [(hevol.hasDerivAt (D.regular_mem_nhds htreg)).deriv]
  calc
    |laplacianAt (flowG S) t (S.scalar t) x +
        2 * normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x)|
        ≤ |laplacianAt (flowG S) t (S.scalar t) x| +
          |2 * normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x)| := abs_add_le _ _
    _ ≤ d ^ 6 * B + 2 * d ^ 4 * K ^ 2 := by
      rw [abs_of_nonneg (by linarith :
        0 ≤ 2 * normSq0S (I := I) (S.family.metric t) x 2 (S.ricci t x))]
      linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_scalar_derivative_bound_of_complete_ancient_bounded_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_scalar_derivative_bound_of_complete_ancient_bounded_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_scalar_derivative_bound_of_complete_ancient_bounded_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_scalar_derivative_bound_of_complete_ancient_bounded_curvature

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem scalar_sub_le_of_derivative_bound
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b C s t : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b)
    (hbound : ∀ r < b, ∀ x : M, |deriv (fun u : ℝ => S.scalar u x) r| ≤ C)
    (hst : s ≤ t) (ht : t ≤ b) (x : M) :
    |S.scalar t x - S.scalar s x| ≤ C * (t - s) := by
  have hmap : Continuous (fun r : ℝ => (r, x)) := continuous_id.prodMk continuous_const
  have hmaps : _root_.Set.MapsTo (fun r : ℝ => (r, x)) (_root_.Set.Icc s t) (D.carrier ×ˢ (_root_.Set.univ : Set M)) :=
    fun r hr => ⟨by rw [hcarrier]; exact hr.2.trans ht, _root_.Set.mem_univ x⟩
  have hcont := hS.scalarCont.comp hmap.continuousOn hmaps
  have hderiv (r : ℝ) (hr : r ∈ _root_.Set.Ico s t) :
      HasDerivWithinAt (fun u : ℝ => S.scalar u x)
        (deriv (fun u : ℝ => S.scalar u x) r) (_root_.Set.Ici r) r := by
    have hrreg : r ∈ D.regular := by rw [hregular]; exact hr.2.trans_le ht
    have hdiff : DifferentiableAt ℝ (fun u : ℝ => S.scalar u x) r :=
      (hS.scalarTime (K := D.carrier) (D.regular_subset hrreg) (fun _ h => h) x).differentiableAt
        (D.regular_mem_nhds hrreg)
    exact hdiff.hasDerivAt.hasDerivWithinAt
  have hnorm : ∀ r ∈ _root_.Set.Ico s t, ‖deriv (fun u : ℝ => S.scalar u x) r‖ ≤ C :=
    fun r hr => hbound r (hr.2.trans_le ht) x
  exact norm_image_sub_le_of_norm_deriv_right_le_segment hcont hderiv hnorm
    t ⟨hst, le_rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.scalar_sub_le_of_derivative_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.scalar_sub_le_of_derivative_bound target :: scope.openDecls } }

theorem exists_scalar_time_lipschitz_bound_of_complete_ancient_bounded_curvature
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b K : ℝ} (hcarrier : D.carrier = _root_.Set.Iic b) (hregular : D.regular = _root_.Set.Iio b)
    (hK : 0 < K)
    (hcomplete : ∀ t ≤ b, RiemannianMetricComplete (I := I) (S.base.metric t))
    (hcurv : ∀ t ≤ b, ∀ x : M,
      normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ K ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ≤ b, ∀ t ≤ b, ∀ x : M,
      |S.scalar s x - S.scalar t x| ≤ C * |s - t| := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_scalar_derivative_bound_of_complete_ancient_bounded_curvature
      S hS hcarrier hregular hK hcomplete hcurv
  refine ⟨C, hC, fun s hs t ht x => ?_⟩
  rcases le_total s t with hst | hts
  · rw [abs_sub_comm (S.scalar s x), abs_sub_comm s, abs_of_nonneg (sub_nonneg.mpr hst)]
    exact scalar_sub_le_of_derivative_bound S hS hcarrier hregular hbound hst ht x
  · rw [abs_of_nonneg (sub_nonneg.mpr hts)]
    exact scalar_sub_le_of_derivative_bound S hS hcarrier hregular hbound hts hs x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.exists_scalar_time_lipschitz_bound_of_complete_ancient_bounded_curvature then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.exists_scalar_time_lipschitz_bound_of_complete_ancient_bounded_curvature"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.exists_scalar_time_lipschitz_bound_of_complete_ancient_bounded_curvature ``Submission.DifferentialGeometry.PDE.RicciFlow.exists_scalar_time_lipschitz_bound_of_complete_ancient_bounded_curvature

end DifferentialGeometry.PDE.RicciFlow
