import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHmJump
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.ChartPushed.MemWkpFour
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2Regularity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.H2RegularitySuccessor
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHmDomainPow
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHmPolymorphic
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.LaplacianDomain.Powers.EvenOrderBridge
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.MeasureTheory _root_.Set _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal _root_.BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace ChartSideH2kBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartPushedMemWkpFour
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapCanonical
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrapPolymorphic
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainPowH2kBridge

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem laplacianDomainPow_succ_exists_resolvent_preimage
    (g : SmoothRiemannianMetric I M) {k : ℕ} (hk_pos : 1 ≤ k)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g (k + 1)) :
    ∃ v_h : H1Compl (I := I) (M := M) g,
      v_h ∈ laplacianDomainPow (I := I) (M := M) g k ∧
      H1ComplToLp (I := I) (M := M) g v_h =
        laplacianDomain.preimage (I := I) (M := M) g
          ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g k hu_h⟩ := by
  classical
  rw [laplacianDomainPow_succ_mem_iff] at hu_h
  obtain ⟨f, hf⟩ := hu_h
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  have h_apply :
      iteratedResolventL2 (I := I) (M := M) g (k' + 1) f =
        resolventL2 (I := I) (M := M) g
          (iteratedResolventL2 (I := I) (M := M) g k' f) :=
    iteratedResolventL2_succ_apply (I := I) (M := M) g k' f
  have h_resolventL2_apply : resolventL2 (I := I) (M := M) g
        (iteratedResolventL2 (I := I) (M := M) g k' f) =
      H1ComplToLp (I := I) (M := M) g
        (resolvent (I := I) (M := M) g
          (iteratedResolventL2 (I := I) (M := M) g k' f)) := by
    rfl
  refine ⟨resolvent (I := I) (M := M) g
    (iteratedResolventL2 (I := I) (M := M) g k' f), ?_, ?_⟩
  · rw [laplacianDomainPow_succ_mem_iff]
    refine ⟨f, rfl⟩
  · apply resolvent_injective (I := I) (M := M) g
    rw [resolvent_laplacianDomain_preimage_eq]
    rw [← h_resolventL2_apply]
    rw [← h_apply]
    exact hf.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.laplacianDomainPow_succ_exists_resolvent_preimage
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.laplacianDomainPow_succ_exists_resolvent_preimage target :: scope.openDecls } }

private theorem chartPushed_memWkp_twoK_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) :
    ∀ (k : ℕ) {u_h : H1Compl (I := I) (M := M) g},
      u_h ∈ laplacianDomainPow (I := I) (M := M) g k →
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) (2 * k) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
  intro k
  induction k with
  | zero =>
      intro u_h _hu_h
      have h_eq : (2 : ℕ) * 0 = 0 := by norm_num
      rw [h_eq]
      exact iteratedH2Regularity_zero (I := I) (M := M) g u_h
  | succ k ih =>
      intro u_h hu_h
      match k, hu_h with
      | 0, hu_h =>
          have h_eq : (2 : ℕ) * 1 = 2 := by norm_num
          rw [h_eq]
          exact (iteratedH2Regularity_one (I := I) (M := M) g hu_h).1
      | 1, hu_h =>
          have h_eq : (2 : ℕ) * 2 = 4 := by norm_num
          rw [h_eq]
          intro α
          exact chartPushed_memWkp_four_two_of_laplacianDomainPow_two
            (I := I) (M := M) g α hu_h
      | k' + 2, hu_h =>
          set kk : ℕ := k' + 2 with hkk_def
          have hkk_ge_2 : 2 ≤ kk := by omega
          have hu_h_kk : u_h ∈ laplacianDomainPow (I := I) (M := M) g kk :=
            laplacianDomainPow_le_of_le (I := I) (M := M) g
              (Nat.le_succ kk) hu_h
          have hu_h_2 : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2 :=
            laplacianDomainPow_le_of_le (I := I) (M := M) g hkk_ge_2 hu_h_kk
          have h_u_kk : DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
              (I := I) (M := M) (2 * kk) 2
              ((H1ComplToLp (I := I) (M := M) g u_h :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
            ih hu_h_kk
          have hkk_pos : 1 ≤ kk := by omega
          obtain ⟨v_h, hv_h_kk, hv_h_eq⟩ :=
            laplacianDomainPow_succ_exists_resolvent_preimage (I := I) (M := M) g
              (k := kk) hkk_pos hu_h
          have h_v_kk : DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
              (I := I) (M := M) (2 * kk) 2
              ((H1ComplToLp (I := I) (M := M) g v_h :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
            ih hv_h_kk
          have h_preimage_2kk : DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
              (I := I) (M := M) (2 * kk) 2
              ((laplacianDomain.preimage (I := I) (M := M) g
                  ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g kk hu_h⟩ :
                Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
            rw [show (laplacianDomain.preimage (I := I) (M := M) g
                  ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                    (I := I) (M := M) g kk hu_h⟩) =
                H1ComplToLp (I := I) (M := M) g v_h from hv_h_eq.symm]
            exact h_v_kk
          have h_2kk_pos : 1 ≤ 2 * kk := by omega
          set m₁ : ℕ := 2 * kk - 1 with hm₁_def
          have hm₁_succ_eq : m₁ + 1 = 2 * kk := by omega
          have hm₁_succ_succ_eq : m₁ + 2 = 2 * kk + 1 := by omega
          have h_chart_H_m1_plus_1_u :
              DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
                (I := I) (M := M) (m₁ + 1) 2
                ((H1ComplToLp (I := I) (M := M) g u_h :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
            rw [hm₁_succ_eq]; exact h_u_kk
          have h_chart_H_m1_RHS :
              DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
                (I := I) (M := M) m₁ 2
                ((laplacianDomain.preimage (I := I) (M := M) g
                    ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                      (I := I) (M := M) g 1 hu_h_2⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
            have h_eq_preimage :
                (laplacianDomain.preimage (I := I) (M := M) g
                    ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                      (I := I) (M := M) g 1 hu_h_2⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =
                (laplacianDomain.preimage (I := I) (M := M) g
                    ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                      (I := I) (M := M) g kk hu_h⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
              congr 1
            rw [h_eq_preimage]
            exact DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart.le_of_le
              (by omega : m₁ ≤ 2 * kk) h_preimage_2kk
          have h_succ_jump_1 :
              ∀ α : M, DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
                (d := Module.finrank ℝ E) (m₁ + 2) 2
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
                  (I := I) (M := M) (chartAtlasPOU I M) α
                  ((H1ComplToLp (I := I) (M := M) g u_h :
                    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                  (I := I) (M := M) α) := by
            intro α
            exact chartPushed_memWkp_succ_jump (I := I) (M := M) g α m₁ hu_h_2
              h_chart_H_m1_plus_1_u h_chart_H_m1_RHS
          have h_chart_H_2kk_plus_1_u :
              DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
                (I := I) (M := M) (2 * kk + 1) 2
                ((H1ComplToLp (I := I) (M := M) g u_h :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
            intro α
            have := h_succ_jump_1 α
            rw [hm₁_succ_succ_eq] at this
            exact this
          set m₂ : ℕ := 2 * kk with hm₂_def
          have hm₂_succ_eq : m₂ + 1 = 2 * kk + 1 := rfl
          have hm₂_succ_succ_eq : m₂ + 2 = 2 * (kk + 1) := by ring
          have h_chart_H_m2_plus_1_u :
              DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
                (I := I) (M := M) (m₂ + 1) 2
                ((H1ComplToLp (I := I) (M := M) g u_h :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
            rw [hm₂_succ_eq]; exact h_chart_H_2kk_plus_1_u
          have h_chart_H_m2_RHS :
              DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
                (I := I) (M := M) m₂ 2
                ((laplacianDomain.preimage (I := I) (M := M) g
                    ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                      (I := I) (M := M) g 1 hu_h_2⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) := by
            have h_eq_preimage :
                (laplacianDomain.preimage (I := I) (M := M) g
                    ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                      (I := I) (M := M) g 1 hu_h_2⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) =
                (laplacianDomain.preimage (I := I) (M := M) g
                    ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
                      (I := I) (M := M) g kk hu_h⟩ :
                  Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) := by
              congr 1
            rw [h_eq_preimage, hm₂_def]
            exact h_preimage_2kk
          have h_succ_jump_2 :
              ∀ α : M, DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
                (d := Module.finrank ℝ E) (m₂ + 2) 2
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
                  (I := I) (M := M) (chartAtlasPOU I M) α
                  ((H1ComplToLp (I := I) (M := M) g u_h :
                    Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                  (I := I) (M := M) α) := by
            intro α
            exact chartPushed_memWkp_succ_jump (I := I) (M := M) g α m₂ hu_h_2
              h_chart_H_m2_plus_1_u h_chart_H_m2_RHS
          intro α
          have := h_succ_jump_2 α
          rw [hm₂_succ_succ_eq] at this
          change DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
              (d := Module.finrank ℝ E) (2 * (k' + 2 + 1)) 2 _ _
          have h_arith : 2 * (kk + 1) = 2 * (k' + 2 + 1) := by
            rw [hkk_def]
          rw [← h_arith]
          exact this

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.chartPushed_memWkp_twoK_of_laplacianDomainPow
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.chartPushed_memWkp_twoK_of_laplacianDomainPow target :: scope.openDecls } }

theorem chartPushed_memWkp_two_k_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (α : M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (2 * k) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) :=
  chartPushed_memWkp_twoK_of_laplacianDomainPow (I := I) (M := M) g k hu_h α

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.chartPushed_memWkp_two_k_of_laplacianDomainPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.chartPushed_memWkp_two_k_of_laplacianDomainPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.chartPushed_memWkp_two_k_of_laplacianDomainPow ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.chartPushed_memWkp_two_k_of_laplacianDomainPow

theorem memWkpChart_two_k_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) :=
  chartPushed_memWkp_twoK_of_laplacianDomainPow (I := I) (M := M) g k hu_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.memWkpChart_two_k_of_laplacianDomainPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.memWkpChart_two_k_of_laplacianDomainPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.memWkpChart_two_k_of_laplacianDomainPow ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.memWkpChart_two_k_of_laplacianDomainPow

theorem chartSideH2kBridge_of_laplacianDomainPow
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    ChartSideH2kBridge (I := I) (M := M) k
      (((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) := by
  intro α
  exact chartPushed_memWkp_two_k_of_laplacianDomainPow
    (I := I) (M := M) g α k hu_h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.chartSideH2kBridge_of_laplacianDomainPow then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.chartSideH2kBridge_of_laplacianDomainPow"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.chartSideH2kBridge_of_laplacianDomainPow ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.chartSideH2kBridge_of_laplacianDomainPow

theorem laplacianDomainPow_memWkpChart_two_k_arbitrary_k
    (g : SmoothRiemannianMetric I M) (k : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g k) :
    DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
      (I := I) (M := M) (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) ∧
    DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart
      (I := I) (M := M) (2 * k) 2
      ((H1ComplToLp (I := I) (M := M) g u_h :
        Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ) < ⊤ := by
  have h_mem := memWkpChart_two_k_of_laplacianDomainPow
    (I := I) (M := M) g k hu_h
  refine ⟨h_mem, ?_⟩
  exact DifferentialGeometry.Analysis.Sobolev.Chart.wkpNormChart_lt_top_of_memWkpChart
    (I := I) (M := M) (k := 2 * k) (p := 2) (by norm_num) h_mem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.laplacianDomainPow_memWkpChart_two_k_arbitrary_k then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.laplacianDomainPow_memWkpChart_two_k_arbitrary_k"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.laplacianDomainPow_memWkpChart_two_k_arbitrary_k ``Submission.DifferentialGeometry.Analysis.Laplacian.ChartSideH2kBridge.laplacianDomainPow_memWkpChart_two_k_arbitrary_k

end ChartSideH2kBridge
end Laplacian
end Analysis
end DifferentialGeometry

end
