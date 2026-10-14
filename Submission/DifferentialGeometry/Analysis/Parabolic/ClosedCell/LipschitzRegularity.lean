import Submission.DifferentialGeometry.Analysis.Parabolic.ClosedCell.SmoothRegularity
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.WeakDerivative.SpatialLp

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
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
  (exists_lp_spatial_weak_derivatives_of_locallyLipschitzOn)

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
  [FiniteDimensional ℝ E]
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

private local instance _root_.Submission.DifferentialGeometry.Analysis.Parabolic.instMeasurableSpaceEuclideanSpaceRealFinFinrankHAddNatOfNat_differentialGeometry : MeasurableSpace W :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ V)) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.instMeasurableSpaceEuclideanSpaceRealFinFinrankHAddNatOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.instMeasurableSpaceEuclideanSpaceRealFinFinrankHAddNatOfNat_differentialGeometry target :: scope.openDecls } }

theorem contDiffOn_affineImage_of_locallyLipschitzOn_weighted_weak_equation
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    {a b : ℝ} (hab : a < b) (hreg : _root_.Set.Icc a b ⊆ D.regular)
    (Ω : Set W) (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω)) :
    let z : W := (toEuclidean (E := V)) c -
      r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
    let Ψ : W → M := fun y => Φ ((toEuclidean (E := V)).symm y)
    let Q : ℝ × W → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
      fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    let Ωh := (fun x => z + r • x) ⁻¹' Ω
    IsCompact (closure Ωh) →
    closure Ωh ⊆ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target →
    ∀ (u : ℝ × W → ℝ), LocallyLipschitzOn (_root_.Set.Icc a b ×ˢ closure Ω) u →
      (∀ φ : ℝ × W → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω →
        (∫ q, Real.sqrt (Q q).det * u q * fderiv ℝ φ q (1, 0)
          ∂(volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) =
          ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
            fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1)
              ∂(volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) →
      ∀ {a' b' : ℝ}, a < a' → b' < b → ∀ {Ω₀ : Set W},
        IsOpen Ω₀ → closure Ω₀ ⊆ Ωh →
        ContDiffOn ℝ (⊤ : ℕ∞) u
          (_root_.Set.Ioo a' b' ×ˢ ((fun x : W => z + r • x) '' Ω₀)) := by
  intro z Ψ Q Ωh hΩhc hΩhs u hu hweak a' b' haa hbb Ω₀ hΩ₀ hΩ₀Ω
  let ν := (volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)
  obtain ⟨U, K, hU, hK, hspatial⟩ :=
    exists_lp_spatial_weak_derivatives_of_locallyLipschitzOn hΩ hΩc hu 2
  have hucont : ContinuousOn u (_root_.Set.Ioo a b ×ˢ Ω) := hu.continuousOn.mono <|
    fun _ hq => ⟨⟨hq.1.1.le, hq.1.2.le⟩, subset_closure hq.2⟩
  have hweakLp (φ : ℝ × W → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
      (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω) :
      (∫ q, Real.sqrt (Q q).det * U q * fderiv ℝ φ q (1, 0) ∂ν) =
        ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) * K i q) *
          fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν := by
    calc
      _ = ∫ q, Real.sqrt (Q q).det * u q * fderiv ℝ φ q (1, 0) ∂ν := by
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [hU] with q hq
        rw [hq]
      _ = ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) *
          fderiv ℝ (fun y => u (q.1, y)) q.2 (EuclideanSpace.single i 1)) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν := hweak φ hφ hφc hφs
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        apply _root_.MeasureTheory.integral_congr_ae
        filter_upwards [ae_all_iff.mpr hK] with q hq
        simp only [hq]
  exact contDiffOn_affineImage_of_continuousOn_weighted_weak_equation
    D g hg Φ c hr hsource α hα hab hreg Ω hΩ hΩhc hΩhs U K u hU hucont
    hspatial hweakLp haa hbb hΩ₀ hΩ₀Ω

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.contDiffOn_affineImage_of_locallyLipschitzOn_weighted_weak_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.contDiffOn_affineImage_of_locallyLipschitzOn_weighted_weak_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.contDiffOn_affineImage_of_locallyLipschitzOn_weighted_weak_equation ``Submission.DifferentialGeometry.Analysis.Parabolic.contDiffOn_affineImage_of_locallyLipschitzOn_weighted_weak_equation

end DifferentialGeometry.Analysis.Parabolic
