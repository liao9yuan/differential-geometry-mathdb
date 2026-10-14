import Submission.DifferentialGeometry.Analysis.Parabolic.ClosedCell.LipschitzRegularity
import Submission.DifferentialGeometry.Topology.Handle.ClosedCell.ChartNeighborhood

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

theorem contDiffOn_of_locallyLipschitzOn_pullback_metric_weak_equation
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    {a b : ℝ} (hab : a < b) (hreg : _root_.Set.Icc a b ⊆ D.regular)
    (Ω : Set W) (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩball : closure Ω ⊆ (toEuclidean (E := V)) '' Metric.ball c r) :
    let Ψ : W → M := fun y => Φ ((toEuclidean (E := V)).symm y)
    let Q : ℝ × W → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
      fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
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
        IsOpen Ω₀ → closure Ω₀ ⊆ Ω →
        ContDiffOn ℝ (⊤ : ℕ∞) u (_root_.Set.Ioo a' b' ×ˢ Ω₀) := by
  intro Ψ Q u hu hweak a' b' haa hbb Ω₀ hΩ₀ hΩ₀Ω
  let α : ClosedCell (m + 1) := ⟨0, by simp⟩
  have hα : ‖α.val‖ < 1 := by simp [α]
  let z : W := (toEuclidean (E := V)) c -
    r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
  let A : W ≃ₜ W := (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft z)
  have hcl (S : Set W) : closure (A ⁻¹' S) = A ⁻¹' closure S :=
    (A.preimage_closure S).symm
  have hcompact : IsCompact (closure (A ⁻¹' Ω)) := by
    rw [hcl]
    exact A.isCompact_preimage.mpr hΩc
  have htarget : closure (A ⁻¹' Ω) ⊆
      toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target := by
    intro y hy
    rw [hcl] at hy
    have hy' := hΩball hy
    have himage := affine_image_closedCell_extChartAt_target
      (toEuclidean (E := V)) α hα c hr
    change (fun y : W => A y) ''
      (toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target) = _ at himage
    rw [← himage] at hy'
    rcases hy' with ⟨x, hx, hxy⟩
    rwa [A.injective hxy] at hx
  have hΩ₀A : IsOpen (A ⁻¹' Ω₀) := hΩ₀.preimage A.continuous
  have hΩ₀sub : closure (A ⁻¹' Ω₀) ⊆ A ⁻¹' Ω := by
    rw [hcl]
    exact _root_.Set.preimage_mono hΩ₀Ω
  have hs := contDiffOn_affineImage_of_locallyLipschitzOn_weighted_weak_equation
    D g hg Φ c hr hsource α hα hab hreg Ω hΩ hΩc hcompact htarget u hu hweak
    haa hbb hΩ₀A hΩ₀sub
  have himage : (fun y : W => z + r • y) '' (A ⁻¹' Ω₀) = Ω₀ := by
    change A '' (A ⁻¹' Ω₀) = Ω₀
    exact A.surjective.image_preimage Ω₀
  change ContDiffOn ℝ (⊤ : ℕ∞) u
    (_root_.Set.Ioo a' b' ×ˢ ((fun y : W => z + r • y) '' (A ⁻¹' Ω₀))) at hs
  rwa [himage] at hs

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.contDiffOn_of_locallyLipschitzOn_pullback_metric_weak_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.contDiffOn_of_locallyLipschitzOn_pullback_metric_weak_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.contDiffOn_of_locallyLipschitzOn_pullback_metric_weak_equation ``Submission.DifferentialGeometry.Analysis.Parabolic.contDiffOn_of_locallyLipschitzOn_pullback_metric_weak_equation

end DifferentialGeometry.Analysis.Parabolic
