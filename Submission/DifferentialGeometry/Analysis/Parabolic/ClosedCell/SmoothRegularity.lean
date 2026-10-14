import Submission.DifferentialGeometry.Analysis.Parabolic.ClosedCell.TimeDerivatives
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.SpacetimeRegularity

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
  (contDiffOn_of_continuousOn_finite_time_weak_partial_trees)

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

theorem contDiffOn_closedCell_of_continuousOn_weighted_weak_equation
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    {a b : ℝ} (hab : a < b) (hreg : _root_.Set.Icc a b ⊆ D.regular)
    (Ω : Set W) (hΩ : IsOpen Ω) :
    let z : W := (toEuclidean (E := V)) c -
      r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
    let Ψ : W → M := fun y => Φ ((toEuclidean (E := V)).symm y)
    let Q : ℝ × W → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
      fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    let Ωh := (fun x => z + r • x) ⁻¹' Ω
    IsCompact (closure Ωh) →
    closure Ωh ⊆ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target →
    ∀ (U : _root_.MeasureTheory.Lp ℝ 2 ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)))
      (K : Fin (Module.finrank ℝ V) →
        _root_.MeasureTheory.Lp ℝ 2 ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)))
      (u : ℝ × W → ℝ),
      (U =ᵐ[(volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)] u) →
      ContinuousOn u (_root_.Set.Ioo a b ×ˢ Ω) →
      (∀ i, ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => K i (t, x)) (fun x => U (t, x)) Ω) →
      (∀ φ : ℝ × W → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω →
        (∫ q, Real.sqrt (Q q).det * U q * fderiv ℝ φ q (1, 0)
          ∂(volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) =
          ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) * K i q) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1)
              ∂(volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) →
      ∀ {a' b' : ℝ}, a < a' → b' < b → ∀ {Ω₀ : Set W},
        IsOpen Ω₀ → closure Ω₀ ⊆ Ωh →
        ContDiffOn ℝ (⊤ : ℕ∞) (fun q : ℝ × W => u (q.1, z + r • q.2))
          (_root_.Set.Ioo a' b' ×ˢ Ω₀) := by
  intro z Ψ Q Ωh hΩhc hΩhs U K u hU hu hspatial hweak a' b' haa hbb Ω₀ hΩ₀ hΩ₀Ω
  let ν := (volume.restrict (_root_.Set.Icc a' b')).prod (volume.restrict Ω₀)
  let νh := (volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ωh)
  have hν : ν ≤ νh := Measure.prod_mono
    (Measure.restrict_mono (_root_.Set.Icc_subset_Icc haa.le hbb.le) le_rfl)
    (Measure.restrict_mono (subset_closure.trans hΩ₀Ω) le_rfl)
  have hmap := quasiMeasurePreserving_prod_add_smul_restrict
    (volume.restrict (_root_.Set.Icc a b)) _root_.MeasureTheory.MeasureSpace.volume z hr.ne' Ω
  have hUlocal : (fun q : ℝ × W => U (q.1, z + r • q.2)) =ᵐ[ν]
      fun q => u (q.1, z + r • q.2) :=
    (hmap.ae hU).filter_mono (_root_.MeasureTheory.ae_mono hν)
  have hulocal : ContinuousOn (fun q : ℝ × W => u (q.1, z + r • q.2))
      (_root_.Set.Ioo a' b' ×ˢ Ω₀) := by
    apply hu.comp (by fun_prop)
    intro q hq
    exact ⟨⟨haa.trans hq.1.1, hq.1.2.trans hbb⟩, hΩ₀Ω (subset_closure hq.2)⟩
  rw [contDiffOn_infty]
  intro s
  let L := s + Module.finrank ℝ V + 2
  have hLs : (s : ℝ) + (Module.finrank ℝ V + 1 : ℝ) / 2 < L := by
    dsimp [L]
    push_cast
    have hn : (0 : ℝ) ≤ Module.finrank ℝ V := Nat.cast_nonneg _
    linarith
  obtain ⟨X, hXroot, _, hXspace, _, hXtime⟩ := exists_closedCell_time_weak_partial_trees
    L L D g hg Φ c hr hsource α hα hab hreg Ω hΩ hΩhc hΩhs U K hspatial hweak
    haa hbb hΩ₀ hΩ₀Ω
  let Y : Fin (L + 1) → ∀ n : ℕ, (Fin n → Fin (Module.finrank ℝ V)) → _root_.MeasureTheory.Lp ℝ 2 ν :=
    fun j => X j.castSucc
  apply contDiffOn_of_continuousOn_finite_time_weak_partial_trees
    hΩ₀ hLs (fun q => u (q.1, z + r • q.2)) hulocal Y
  · exact hXroot.trans hUlocal
  · intro j n hjn β i
    exact hXspace j.castSucc n (by dsimp [L] at *; omega) β i
  · intro j n hjn β φ hφ hφc hφs
    have h := hXtime j.castSucc n (by dsimp [L] at *; omega) β φ hφ hφc hφs
    simpa only [Y, Fin.castSucc_succ] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.contDiffOn_closedCell_of_continuousOn_weighted_weak_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.contDiffOn_closedCell_of_continuousOn_weighted_weak_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.contDiffOn_closedCell_of_continuousOn_weighted_weak_equation ``Submission.DifferentialGeometry.Analysis.Parabolic.contDiffOn_closedCell_of_continuousOn_weighted_weak_equation

theorem contDiffOn_affineImage_of_continuousOn_weighted_weak_equation
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    {a b : ℝ} (hab : a < b) (hreg : _root_.Set.Icc a b ⊆ D.regular)
    (Ω : Set W) (hΩ : IsOpen Ω) :
    let z : W := (toEuclidean (E := V)) c -
      r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
    let Ψ : W → M := fun y => Φ ((toEuclidean (E := V)).symm y)
    let Q : ℝ × W → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
      fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    let Ωh := (fun x => z + r • x) ⁻¹' Ω
    IsCompact (closure Ωh) →
    closure Ωh ⊆ toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target →
    ∀ (U : _root_.MeasureTheory.Lp ℝ 2 ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)))
      (K : Fin (Module.finrank ℝ V) →
        _root_.MeasureTheory.Lp ℝ 2 ((volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)))
      (u : ℝ × W → ℝ),
      (U =ᵐ[(volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)] u) →
      ContinuousOn u (_root_.Set.Ioo a b ×ˢ Ω) →
      (∀ i, ∀ᵐ t ∂volume.restrict (_root_.Set.Icc a b), DeGiorgi.HasWeakPartialDeriv i
        (fun x => K i (t, x)) (fun x => U (t, x)) Ω) →
      (∀ φ : ℝ × W → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ _root_.Set.Ioo a b ×ˢ Ω →
        (∫ q, Real.sqrt (Q q).det * U q * fderiv ℝ φ q (1, 0)
          ∂(volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) =
          ∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) * K i q) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1)
              ∂(volume.restrict (_root_.Set.Icc a b)).prod (volume.restrict Ω)) →
      ∀ {a' b' : ℝ}, a < a' → b' < b → ∀ {Ω₀ : Set W},
        IsOpen Ω₀ → closure Ω₀ ⊆ Ωh →
        ContDiffOn ℝ (⊤ : ℕ∞) u
          (_root_.Set.Ioo a' b' ×ˢ ((fun x : W => z + r • x) '' Ω₀)) := by
  intro z Ψ Q Ωh hΩhc hΩhs U K u hU hu hspatial hweak a' b' haa hbb Ω₀ hΩ₀ hΩ₀Ω
  have hs := contDiffOn_closedCell_of_continuousOn_weighted_weak_equation
    D g hg Φ c hr hsource α hα hab hreg Ω hΩ hΩhc hΩhs U K u hU hu hspatial hweak
    haa hbb hΩ₀ hΩ₀Ω
  let B : ℝ × W → ℝ × W := fun q => (q.1, r⁻¹ • (q.2 - z))
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := by fun_prop
  have hmaps : _root_.Set.MapsTo B (_root_.Set.Ioo a' b' ×ˢ ((fun x : W => z + r • x) '' Ω₀))
      (_root_.Set.Ioo a' b' ×ˢ Ω₀) := by
    rintro q ⟨ht, x, hx, heq⟩
    refine ⟨ht, ?_⟩
    change r⁻¹ • (q.2 - z) ∈ Ω₀
    rw [← heq, add_sub_cancel_left, inv_smul_smul₀ hr.ne']
    exact hx
  have hcomp := hs.comp hB.contDiffOn hmaps
  have heq : (fun q : ℝ × W => u (q.1, z + r • q.2)) ∘ B = u := by
    funext q
    dsimp [B]
    rw [smul_inv_smul₀ hr.ne', add_sub_cancel]
  rwa [heq] at hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.contDiffOn_affineImage_of_continuousOn_weighted_weak_equation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.contDiffOn_affineImage_of_continuousOn_weighted_weak_equation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.contDiffOn_affineImage_of_continuousOn_weighted_weak_equation ``Submission.DifferentialGeometry.Analysis.Parabolic.contDiffOn_affineImage_of_continuousOn_weighted_weak_equation

end DifferentialGeometry.Analysis.Parabolic
