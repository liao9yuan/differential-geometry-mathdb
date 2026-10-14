import Submission.DifferentialGeometry.Analysis.Sobolev.Nirenberg.H2Regularity.SmoothWeakSolutionH2
import Submission.DifferentialGeometry.Analysis.Sobolev.Solutions.FriedrichsCommutator

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Metric _root_.Filter _root_.Topology _root_.Set _root_.Function
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergCrossBounds
open scoped _root_.ENNReal _root_.NNReal _root_.Convolution _root_.Pointwise _root_.BigOperators _root_.InnerProductSpace
  RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma memLp_two_of_continuous_compact_closure
    {f : E → ℝ} (hf : Continuous f)
    {S : Set E} (hS_open : IsOpen S) (hS_cc : IsCompact (closure S)) :
    MemLp f 2 (volume.restrict S) := by
  have h_volume_closure_lt_top : _root_.MeasureTheory.MeasureSpace.volume (closure S) < ⊤ :=
    hS_cc.measure_lt_top
  have h_volume_lt_top : _root_.MeasureTheory.MeasureSpace.volume S < ⊤ :=
    lt_of_le_of_lt (_root_.MeasureTheory.measure_mono subset_closure) h_volume_closure_lt_top
  have : _root_.MeasureTheory.IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact h_volume_lt_top
  obtain ⟨M, hM⟩ := hS_cc.bddAbove_image hf.abs.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable (_root_.Max.max M 0) ?_
  rw [_root_.MeasureTheory.ae_restrict_iff' hS_open.measurableSet]
  refine Filter.Eventually.of_forall ?_
  intro x hx
  have h_in_closure : x ∈ closure S := subset_closure hx
  have h := hM (Set.mem_image_of_mem _ h_in_closure)
  rw [Real.norm_eq_abs]
  exact h.trans (le_max_left _ _)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.memLp_two_of_continuous_compact_closure
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.memLp_two_of_continuous_compact_closure target :: scope.openDecls } }

structure SmoothApproximation
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (_u _f : E → ℝ) where
  uSeq : ℕ → E → ℝ
  fSeq : ℕ → E → ℝ
  u_seq_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (uSeq n)
  is_smooth_weak_solution :
    ∀ n, B.IsSmoothWeakSolution (uSeq n) (fSeq n)
  f_seq_l2_local :
    ∀ n {S : Set E}, IsCompact (closure S) →
      _root_.MeasureTheory.MemLp (fSeq n) 2 (volume.restrict S)
  u_seq_l2_local :
    ∀ n {S : Set E}, IsCompact (closure S) →
      _root_.MeasureTheory.MemLp (uSeq n) 2 (volume.restrict S)
  grad_seq_l2_local :
    ∀ n {S : Set E}, IsCompact (closure S) →
      ∀ j : Fin d,
        _root_.MeasureTheory.MemLp (fun y : E => (fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1))
          2 (volume.restrict S)
  dataBound : ℝ
  data_bound_nn : 0 ≤ dataBound
  data_integrated_bound :
    ∀ {Ω' : Set E}, IsOpen Ω' → IsCompact (closure Ω') →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
        (∫ y in Ω',
            ∑ j : Fin d,
              ((fderiv ℝ (uSeq n) y) (EuclideanSpace.single j 1)) ^ 2
          ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) +
        (∫ y in Ω', (uSeq n y) ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) +
        (∫ y in Ω', (fSeq n y) ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) ≤
          C * dataBound

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.SmoothApproximation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.SmoothApproximation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.SmoothApproximation ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.SmoothApproximation

private lemma local_per_n_smooth_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω)
    (S : SmoothApproximation B u f)
    (i k : Fin d) (n : ℕ) :
    ∃ g : E → ℝ,
      _root_.MeasureTheory.MemLp g 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g
        (fun y : E => (fderiv ℝ (S.uSeq n) y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ Ω' : Set E, IsOpen Ω' ∧ closure Ω'' ⊆ Ω' ∧ closure Ω' ⊆ Ω ∧
        IsCompact (closure Ω') ∧
        ∃ C : ℝ, 0 ≤ C ∧
          ∫ x in Ω'', g x ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤
            C * (∫ x in Ω',
                  ∑ j : Fin d,
                    ((fderiv ℝ (S.uSeq n) x) (EuclideanSpace.single j 1)) ^ 2
                ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) +
              ∫ x in Ω', (S.uSeq n x) ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) +
              ∫ x in Ω', (S.fSeq n x) ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E)) := by
  obtain ⟨C, hC_nn, h_eng⟩ := local_smooth_solution (d := d) B
    hΩ'' hΩ''_compact_closure h_room
  obtain ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, hbound⟩ :=
    h_eng (S.is_smooth_weak_solution n) (S.f_seq_l2_local n) i k
  exact ⟨g, hg_memLp, hg_weak, Ω', hΩ'_open, hΩ''_in_Ω', hΩ'_in,
    hΩ'_compact, C, hC_nn, hbound⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.local_per_n_smooth_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.local_per_n_smooth_bound target :: scope.openDecls } }

theorem local_nonsmooth_per_n_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω)
    (S : SmoothApproximation B u f) :
    ∀ i k : Fin d, ∀ n : ℕ, ∃ g : E → ℝ,
      _root_.MeasureTheory.MemLp g 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g
        (fun y : E =>
          (fderiv ℝ (S.uSeq n) y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ K : ℝ, 0 ≤ K ∧
        ∫ x in Ω'', g x ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤ K * S.dataBound := by
  classical
  intro i k n
  obtain ⟨g, hg_l2, hg_partial, Ω', hΩ'_open, _hΩ''_in_Ω', _hΩ'_in_Ω,
      hΩ'_compact, C, hC_nn, hC_bound⟩ :=
    local_per_n_smooth_bound (d := d) B hΩ'' hΩ''_compact_closure
      h_room S i k n
  obtain ⟨D, hD_nn, hD_bound⟩ :=
    S.data_integrated_bound (Ω' := Ω') hΩ'_open hΩ'_compact
  refine ⟨g, hg_l2, hg_partial, C * D,
    mul_nonneg hC_nn hD_nn, ?_⟩
  have h_data_le := hD_bound n
  refine hC_bound.trans ?_
  calc C * _
      ≤ C * (D * S.dataBound) :=
        mul_le_mul_of_nonneg_left h_data_le hC_nn
    _ = (C * D) * S.dataBound := by ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.local_nonsmooth_per_n_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.local_nonsmooth_per_n_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.local_nonsmooth_per_n_bound ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.local_nonsmooth_per_n_bound

theorem local_nonsmooth_solution
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u f : E → ℝ}
    {Ω'' : Set E} (hΩ'' : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    (h_room : Metric.cthickening 2 (closure Ω'') ⊆ Ω)
    (S : SmoothApproximation B u f) :
    ∀ i k : Fin d, ∀ n : ℕ, ∃ g_n : E → ℝ,
      _root_.MeasureTheory.MemLp g_n 2 (volume.restrict Ω'') ∧
      DeGiorgi.HasWeakPartialDeriv (d := d) k g_n
        (fun y : E =>
          (fderiv ℝ (S.uSeq n) y) (EuclideanSpace.single i 1)) Ω'' ∧
      ∃ K : ℝ, 0 ≤ K ∧
        ∫ x in Ω'', g_n x ^ 2 ∂(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure E) ≤ K * S.dataBound :=
  local_nonsmooth_per_n_bound (d := d) B hΩ'' hΩ''_compact_closure
    h_room S

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.local_nonsmooth_solution then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.local_nonsmooth_solution"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.local_nonsmooth_solution ``Submission.DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth.local_nonsmooth_solution

end DifferentialGeometry.Analysis.Sobolev.NirenbergNonSmooth
