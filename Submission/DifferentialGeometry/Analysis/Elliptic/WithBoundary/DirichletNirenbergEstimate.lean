import Submission.DifferentialGeometry.Analysis.Integration.LpNorm
import Submission.DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletNirenbergIntegration
import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.TestFunction.NormBounds

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Metric _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Topology

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry : MeasurableSpace M := borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry target :: scope.openDecls } }


open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergTestFunction

theorem exists_integral_cutoff_sq_diffQuot_chartInverse_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω Ω' Ω'' : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    {η : EuStd → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω'') {r : ℝ} (hr : 0 < r)
    (hroom : Metric.cthickening r (closure Ω'') ⊆ Ω') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : Fin (Module.finrank ℝ EuN)) (h : ℝ)
      (_ : |h| ≤ r) (u : H1ComplDirichlet q),
      let x := fun z => (extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z)
      (∫ z, η z ^ 2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun z => H1ComplDirichletToLp q u (x z)) z) ^ 2) ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨A, hηbound⟩ := hηc.exists_bound_of_continuous hη
  have hA : 0 ≤ A := (norm_nonneg (η 0)).trans (hηbound 0)
  let D := fun k => dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k
  let K : ℝ := ∑ k, ‖D k‖
  refine ⟨A ^ 2 * K ^ 2, mul_nonneg (sq_nonneg _) (sq_nonneg _), ?_⟩
  intro k h hh u
  let U := fun z => H1ComplDirichletToLp q u
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  have hu : _root_.MeasureTheory.MemLp U 2 (volume.restrict Ω) :=
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u).memLp
  have hd := hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k u
  have hb := integral_cutoff_sq_diffQuot_le_eLpNorm_weakPartial_sq hΩ hΩ' hΩ''
    hΩ'c hΩ'Ω hΩ''c hu (Lp.memLp (D k u)) hη hηc hηs hA
    (fun x => by simpa only [Real.norm_eq_abs] using hηbound x) k hd hr hroom hh
  have hnorm : (_root_.MeasureTheory.eLpNorm (D k u) 2 (volume.restrict Ω')).toReal ≤ K * ‖u‖ := by
    calc
      _ ≤ (_root_.MeasureTheory.eLpNorm (D k u) 2 (volume.restrict Ω)).toReal :=
        ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (_root_.MeasureTheory.eLpNorm_mono_measure _
          (Measure.restrict_mono (subset_closure.trans hΩ'Ω) le_rfl))
      _ = ‖D k u‖ := (Lp.norm_def _).symm
      _ ≤ ‖D k‖ * ‖u‖ := (D k).le_opNorm u
      _ ≤ K * ‖u‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact Finset.single_le_sum (fun i _ => norm_nonneg (D i)) (Finset.mem_univ k)
  change (∫ z, η z ^ 2 * (DifferentialGeometry.Analysis.Sobolev.diffQuot k h U z) ^ 2) ≤ _
  calc
    _ ≤ A ^ 2 * (_root_.MeasureTheory.eLpNorm (D k u) 2 (volume.restrict Ω')).toReal ^ 2 := hb
    _ ≤ A ^ 2 * (K * ‖u‖) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ENNReal.toReal_nonneg hnorm 2) (sq_nonneg _)
    _ = _ := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_integral_cutoff_sq_diffQuot_chartInverse_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_integral_cutoff_sq_diffQuot_chartInverse_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_integral_cutoff_sq_diffQuot_chartInverse_le ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_integral_cutoff_sq_diffQuot_chartInverse_le

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet


namespace DifferentialGeometry.Analysis.Sobolev

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem eLpNorm_restrict_apply_le
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    {Ω K : Set E} (D : V →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω)) (hKΩ : K ⊆ Ω) (u : V) :
    (_root_.MeasureTheory.eLpNorm (D u) 2 (volume.restrict K)).toReal ≤ ‖D‖ * ‖u‖ := by
  calc
    _ ≤ (_root_.MeasureTheory.eLpNorm (D u) 2 (volume.restrict Ω)).toReal :=
      ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
        (_root_.MeasureTheory.eLpNorm_mono_measure _ (Measure.restrict_mono hKΩ le_rfl))
    _ = ‖D u‖ := (Lp.norm_def _).symm
    _ ≤ ‖D‖ * ‖u‖ := D.le_opNorm u

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.eLpNorm_restrict_apply_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.eLpNorm_restrict_apply_le target :: scope.openDecls } }

private theorem integral_sq_restrict_apply_le
    {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    {Ω K : Set E} (D : V →L[ℝ] _root_.MeasureTheory.Lp ℝ 2 (volume.restrict Ω)) (hKΩ : K ⊆ Ω) (u : V) :
    (∫ z in K, (D u z)^2) ≤ ‖D‖^2 * ‖u‖^2 := by
  rw [Analysis.Integration.integral_sq_eq_l2
    ((Lp.memLp (D u)).mono_measure (Measure.restrict_mono hKΩ le_rfl))]
  calc
    _ ≤ (‖D‖ * ‖u‖)^2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg (eLpNorm_restrict_apply_le D hKΩ u) 2
    _ = _ := mul_pow _ _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.integral_sq_restrict_apply_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.integral_sq_restrict_apply_le target :: scope.openDecls } }

end DifferentialGeometry.Analysis.Sobolev

namespace DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet

open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "EuStd" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry_1 : MeasurableSpace EuStd :=
  WithLp.measurableSpace 2 ((i : Fin (Module.finrank ℝ EuN)) → ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.instMeasurableSpaceEuclideanSpaceRealFinFinrank_differentialGeometry_1 target :: scope.openDecls } }

theorem exists_integral_sq_weakPartial_diffQuot_chartInverse_le
    (q : SmoothRiemannianMetric I_hs M) (α : M) {Ω K : Set EuStd}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuN) '' interior (extChartAt I_hs α).target)
    (hK : IsCompact K) (hKs : K ⊆ Ω) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ, 0 ≤ C ∧ Metric.cthickening δ K ⊆ Ω ∧
      ∀ (k : Fin (Module.finrank ℝ EuN)) (s : ℝ), |s| ≤ δ →
        ∀ u : H1ComplDirichlet q,
        let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
        let U := fun z => H1ComplDirichletToLp q u
          ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
        (∑ i, ∫ z in K, (D i u z)^2) + ∫ z in K, (diffQuot k s U z)^2 ≤ C * ‖u‖^2 := by
  obtain ⟨Ω', hΩ', hKΩ', hΩ'Ω, hΩ'c⟩ :=
    exists_open_between_and_isCompact_closure hK hΩ hKs
  obtain ⟨Ω'', hΩ'', hKΩ'', hΩ''Ω', hΩ''c⟩ :=
    exists_open_between_and_isCompact_closure hK hΩ' hKΩ'
  obtain ⟨δ, hδ, hδroom⟩ := hΩ''c.exists_cthickening_subset_open hΩ' hΩ''Ω'
  have hδΩ : _root_.Metric.cthickening δ K ⊆ Ω :=
    (_root_.Metric.cthickening_subset_of_subset δ (hKΩ''.trans subset_closure)).trans
      (hδroom.trans (subset_closure.trans hΩ'Ω))
  let D := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs
  let C : ℝ := ∑ i, ‖D i‖^2
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine ⟨δ, hδ, 2*C, by positivity, hδΩ, ?_⟩
  intro k s hs u
  let U := fun z => H1ComplDirichletToLp q u
    ((extChartAt I_hs α).symm ((toEuclidean (E := EuN)).symm z))
  have hU : _root_.MeasureTheory.MemLp U 2 (volume.restrict Ω) :=
    (memWkp_chartInverse_H1ComplDirichletToLp q α hΩ hΩc hΩs u).memLp
  have hnorm (i) : (_root_.MeasureTheory.eLpNorm (D i u) 2 (volume.restrict Ω')).toReal ≤ ‖D i‖ * ‖u‖ :=
    eLpNorm_restrict_apply_le (D i) (subset_closure.trans hΩ'Ω) u
  have hgrad (i) : (∫ z in K, (D i u z)^2) ≤ ‖D i‖^2 * ‖u‖^2 :=
    integral_sq_restrict_apply_le (D i) hKs u
  have hdiff : (∫ z in K, (diffQuot k s U z)^2) ≤ C * ‖u‖^2 := by
    have hmem := memLp_diffQuot_restrict hΩ.measurableSet hK.measurableSet hU k s
      ((_root_.Metric.cthickening_mono hs K).trans hδΩ)
    rw [Analysis.Integration.integral_sq_eq_l2 hmem]
    have hd := eLpNorm_diffQuot_le_eLpNorm_weakPartial_local hΩ hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c
      hU (Lp.memLp (D k u)) k (hasWeakPartialDeriv_dirichletLocalWeakPartialLp q α hΩ hΩc hΩs k u)
      hδ hδroom hs
    have hb : (_root_.MeasureTheory.eLpNorm (diffQuot k s U) 2 (volume.restrict K)).toReal ≤ ‖D k‖ * ‖u‖ := by
      calc
        _ ≤ (_root_.MeasureTheory.eLpNorm (D k u) 2 (volume.restrict Ω')).toReal :=
          ENNReal.toReal_mono ((Lp.memLp (D k u)).mono_measure
            (Measure.restrict_mono (subset_closure.trans hΩ'Ω) le_rfl)).eLpNorm_ne_top
            ((_root_.MeasureTheory.eLpNorm_mono_measure _ (Measure.restrict_mono hKΩ'' le_rfl)).trans hd)
        _ ≤ _ := hnorm k
    calc
      _ ≤ (‖D k‖ * ‖u‖)^2 := pow_le_pow_left₀ ENNReal.toReal_nonneg hb 2
      _ = ‖D k‖^2 * ‖u‖^2 := mul_pow _ _ _
      _ ≤ C * ‖u‖^2 := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun i _ => sq_nonneg ‖D i‖) (Finset.mem_univ k)) (sq_nonneg _)
  change (∑ i, ∫ z in K, (D i u z)^2) + ∫ z in K, (diffQuot k s U z)^2 ≤ _
  calc
    _ ≤ (∑ i, ‖D i‖^2 * ‖u‖^2) + C * ‖u‖^2 :=
      add_le_add (Finset.sum_le_sum fun i _ => hgrad i) hdiff
    _ = _ := by rw [← Finset.sum_mul]; ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_integral_sq_weakPartial_diffQuot_chartInverse_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_integral_sq_weakPartial_diffQuot_chartInverse_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_integral_sq_weakPartial_diffQuot_chartInverse_le ``Submission.DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet.exists_integral_sq_weakPartial_diffQuot_chartInverse_le

end DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
