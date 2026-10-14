import Submission.DifferentialGeometry.Analysis.Elliptic.MetricExtension.ClosedCellAffineDensity
import Submission.DifferentialGeometry.Analysis.Parabolic.WeakEquation.AffineLpTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Matrix _root_.Submission.Matrix _root_.Topology

namespace DifferentialGeometry.Analysis.Parabolic

open _root_.Submission.DifferentialGeometry.Analysis.Laplacian
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Topology
open _root_.Submission.DifferentialGeometry.Topology.Handle

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.instChartedSpaceEuclideanHalfSpaceHAddNatOfNatClosedCell target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell (m : ℕ) :
    IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  closedCellIsManifold m

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.instIsManifoldRealEuclideanSpaceFinHAddNatOfNatEuclideanHalfSpaceModelWithCornersEuclideanHalfSpaceSomeENatTopClosedCell target :: scope.openDecls } }

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin (m + 1))
local notation "W" => EuclideanSpace ℝ (Fin (Module.finrank ℝ V))

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.instT2SpaceEuclideanSpaceRealFinHAddNatOfNat_differentialGeometry : T2Space V := inferInstance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.instT2SpaceEuclideanSpaceRealFinHAddNatOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.instT2SpaceEuclideanSpaceRealFinHAddNatOfNat_differentialGeometry target :: scope.openDecls } }

theorem exists_closedCell_lp_weighted_weak_equation
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    (μ : _root_.MeasureTheory.Measure ℝ) [_root_.MeasureTheory.SFinite μ] (J : Set ℝ) (Ω : Set W) :
    let b : W := (toEuclidean (E := V)) c -
      r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
    let Ψ : W → M := fun z => Φ ((toEuclidean (E := V)).symm z)
    let Q : ℝ × W → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
      fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    ((fun x => b + r • x) ⁻¹' Ω ⊆
      toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target) →
    ∀ {p : ℝ≥0∞} (U F : _root_.MeasureTheory.Lp ℝ p (μ.prod (volume.restrict Ω)))
      (K : Fin (Module.finrank ℝ V) → _root_.MeasureTheory.Lp ℝ p (μ.prod (volume.restrict Ω))),
      (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
        (fun x => K k (t, x)) (fun x => U (t, x)) Ω) →
      (∀ φ : ℝ × W → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ J ×ˢ Ω →
        (∫ q, Real.sqrt (Q q).det * U q * fderiv ℝ φ q (1, 0)
          ∂μ.prod (volume.restrict Ω)) =
          (∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) * K i q) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω)) -
          ∫ q, F q * φ q ∂μ.prod (volume.restrict Ω)) →
      let ν := μ.prod (volume.restrict ((fun x => b + r • x) ⁻¹' Ω))
      ∃ Uh Fh : _root_.MeasureTheory.Lp ℝ p ν, ∃ Kh : Fin (Module.finrank ℝ V) → _root_.MeasureTheory.Lp ℝ p ν,
        (Uh =ᵐ[ν] fun q => U (q.1, b + r • q.2)) ∧
        (Fh =ᵐ[ν] fun q => r ^ Module.finrank ℝ V * F (q.1, b + r • q.2)) ∧
        (∀ i, Kh i =ᵐ[ν] fun q => r * K i (q.1, b + r • q.2)) ∧
        (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
          (fun x => Kh k (t, x)) (fun x => Uh (t, x))
          ((fun x => b + r • x) ⁻¹' Ω)) ∧
        ∀ φ : ℝ × W → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
          HasCompactSupport φ → tsupport φ ⊆ J ×ˢ ((fun x => b + r • x) ⁻¹' Ω) →
          (∫ q, MetricExtension.densityOnEuclid
              ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric q.1) α q.2 *
            Uh q * fderiv ℝ φ q (1, 0) ∂ν) =
            (∑ j, ∫ q, (∑ i, MetricExtension.weightedInvGramOnEuclid
                ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric q.1) α i j q.2 *
              Kh i q) * fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν) -
            ∫ q, Fh q * φ q ∂ν := by
  intro b Ψ Q hΩ p U F K hspatial hweak ν
  let ρ : ℝ × W → ℝ := fun q => Real.sqrt (Q q).det
  let A := fun i j (q : ℝ × W) => Real.sqrt (Q q).det * (Q q)⁻¹ i j
  let S : ℝ × W → ℝ × W := fun q => (q.1, b + r • q.2)
  let δ := |r ^ Module.finrank ℝ V|
  have hδ : δ = r ^ Module.finrank ℝ V := abs_of_pos (pow_pos hr _)
  obtain ⟨Uh, Fh, Kh, hU, hF, hK, hspatialH, hweakH⟩ :=
    exists_lp_weighted_weak_equation_comp_add_smul μ J Ω ρ A U F K
      hspatial hweak b hr.ne'
  refine ⟨Uh, Fh, Kh, hU, ?_, hK, hspatialH, ?_⟩
  · simpa only [abs_of_pos (pow_pos hr _)] using hF
  · intro φ hφ hφc hφs
    have hρ (q : ℝ × W) (hq : q.2 ∈ (fun x => b + r • x) ⁻¹' Ω) :
        MetricExtension.densityOnEuclid
            ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric q.1) α q.2 =
          δ * ρ (S q) := by
      rw [hδ]
      exact MetricExtension.densityOnEuclid_closedCellPullbackMetricFamily_affine
        D g Φ c hr hsource q.1 α hα (hΩ hq)
    have hA (q : ℝ × W) (hq : q.2 ∈ (fun x => b + r • x) ⁻¹' Ω)
        (i j : Fin (Module.finrank ℝ V)) :
        MetricExtension.weightedInvGramOnEuclid
            ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric q.1) α i j q.2 =
          (δ / r ^ 2) * A i j (S q) := by
      rw [hδ]
      exact MetricExtension.weightedInvGramOnEuclid_closedCellPullbackMetricFamily_affine
        D g Φ c hr hsource q.1 α hα (hΩ hq) i j
    have hzero (q : ℝ × W) (hq : q.2 ∉ (fun x => b + r • x) ⁻¹' Ω)
        (v : ℝ × W) : fderiv ℝ φ q v = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun x : ℝ × W => fderiv ℝ φ x v)
        (fun h => hq (hφs ((tsupport_fderiv_apply_subset ℝ v) h)).2)
    have hleft :
        (∫ q, MetricExtension.densityOnEuclid
            ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric q.1) α q.2 *
          Uh q * fderiv ℝ φ q (1, 0) ∂ν) =
          ∫ q, (δ * ρ (S q)) * Uh q * fderiv ℝ φ q (1, 0) ∂ν := by
      apply _root_.MeasureTheory.integral_congr_ae
      refine Filter.Eventually.of_forall fun q => ?_
      dsimp only
      by_cases hq : q.2 ∈ (fun x => b + r • x) ⁻¹' Ω
      · rw [hρ q hq]
      · simp only [hzero q hq (1, 0), _root_.MulZeroClass.mul_zero]
    have hright (j : Fin (Module.finrank ℝ V)) :
        (∫ q, (∑ i, MetricExtension.weightedInvGramOnEuclid
            ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric q.1) α i j q.2 *
          Kh i q) * fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν) =
          ∫ q, (∑ i, (δ / r ^ 2 * A i j (S q)) * Kh i q) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν := by
      apply _root_.MeasureTheory.integral_congr_ae
      refine Filter.Eventually.of_forall fun q => ?_
      dsimp only
      by_cases hq : q.2 ∈ (fun x => b + r • x) ⁻¹' Ω
      · simp only [hA q hq]
      · simp only [hzero q hq (0, EuclideanSpace.single j 1), _root_.MulZeroClass.mul_zero]
    rw [hleft]
    simp only [hright]
    exact hweakH φ hφ hφc hφs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.exists_closedCell_lp_weighted_weak_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.exists_closedCell_lp_weighted_weak_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.exists_closedCell_lp_weighted_weak_equation ``Submission.DifferentialGeometry.Analysis.Parabolic.exists_closedCell_lp_weighted_weak_equation

end DifferentialGeometry.Analysis.Parabolic
