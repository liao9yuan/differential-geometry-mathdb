import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.VariationalIdentity.DifferentiatedData
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.VariationalIdentity.InductiveSuccessor
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.BaseFChart.PolymorphicRegularity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.EffectiveSourceSuccessorRegularity
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.InteriorH2RelaxedHyp
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.Bootstrap.ChartHm
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.Iterated.NirenbergInterior.MixedPartials
import Submission.DifferentialGeometry.Analysis.Elliptic.Regularity.DiffChart.Differentiated.CanonicalDerivedData

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.MeasureTheory _root_.Filter _root_.Topology _root_.Function
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix _root_.InnerProductSpace _root_.BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace IteratedChartHmJump

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.MetricExtension
  hiding chartTargetEuclid chartTargetEuclid_isOpen
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.ChartBilinearH1Compl
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedMixedPartials
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedDifferentiatedData
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedVariationalIdentityStep
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedBaseFChartRegularityB
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedEffectiveSourceSuccessorRegularity
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedNirenbergInteriorWeakened
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmBootstrap
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedVariationalIdentitySuccessorSource
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.LaplacianDomainChartData
open _root_.Submission.DifferentialGeometry.Analysis.Laplacian.CanonicalDerivedChartBilinearH1ComplData
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Chart
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean

private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private noncomputable def padDirs {n : ℕ}
    (dirs : Fin n → Fin (Module.finrank ℝ E)) :
    ℕ → Fin (Module.finrank ℝ E) :=
  fun j => if h : j < n then dirs ⟨j, h⟩ else
    ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.padDirs
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.padDirs target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
@[simp] private lemma padDirs_at_lt {n : ℕ}
    (dirs : Fin n → Fin (Module.finrank ℝ E))
    {j : ℕ} (hj : j < n) :
    padDirs dirs j = dirs ⟨j, hj⟩ := by
  unfold padDirs; rw [dif_pos hj]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.padDirs_at_lt
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.padDirs_at_lt target :: scope.openDecls } }

private noncomputable def dirsOf {n : ℕ}
    (dirs : Fin n → Fin (Module.finrank ℝ E)) (k : ℕ) :
    Fin k → Fin (Module.finrank ℝ E) :=
  fun i => padDirs dirs i.val

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.dirsOf
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.dirsOf target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
@[simp] private lemma dirsOf_zero {n : ℕ}
    (dirs : Fin n → Fin (Module.finrank ℝ E)) :
    dirsOf dirs 0 = Fin.elim0 := by
  funext i; exact i.elim0

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.dirsOf_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.dirsOf_zero target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma dirsOf_succ {n : ℕ}
    (dirs : Fin n → Fin (Module.finrank ℝ E)) (k : ℕ) :
    dirsOf dirs (k + 1) =
      Fin.snoc (dirsOf dirs k) (padDirs dirs k) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hlast
  · subst hj
    rw [Fin.snoc_castSucc]
    rfl
  · subst hlast
    rw [Fin.snoc_last]
    rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.dirsOf_succ
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.dirsOf_succ target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] in
private lemma dirsOf_self {n : ℕ}
    (dirs : Fin n → Fin (Module.finrank ℝ E)) :
    dirsOf dirs n = dirs := by
  funext i
  unfold dirsOf
  rw [padDirs_at_lt dirs i.isLt]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.dirsOf_self
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.dirsOf_self target :: scope.openDecls } }

private structure LevelBundle
    (g : SmoothRiemannianMetric I M) (α : M)
    {n : ℕ} (dirs : Fin n → Fin (Module.finrank ℝ E))
    {u_h : H1Compl (I := I) (M := M) g}
    (_hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (m j : ℕ) where
  data : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h j
  directions_eq : data.directions = dirsOf dirs j
  fChartEffective_memWkp :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m - j) 2 data.diffChartForcing
      (chartTargetEuclid (I := I) (M := M) α)
  fChartEffective_ae_zero_off_K :
    data.diffChartForcing =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
      (chartTargetEuclid (I := I) (M := M) α \
        chartImagePOUTsupport (I := I) (M := M) α)]
      (fun _ : EuclN => (0 : ℝ))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.LevelBundle
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.LevelBundle target :: scope.openDecls } }

private def buildLevelZero
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (m : ℕ)
    {n : ℕ} (dirs : Fin n → Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_1_u :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) (m + 1) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    (h_chart_H_m_RHS :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) m 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    LevelBundle (I := I) (M := M) g α dirs hu_h m 0 :=
  { data := IteratedDiffChartBilinearData.ofBase (I := I) (M := M) g α hu_h
    directions_eq := by
      change (Fin.elim0 : Fin 0 → Fin (Module.finrank ℝ E)) = dirsOf dirs 0
      rw [dirsOf_zero]
    fChartEffective_memWkp := by
      change DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m - 0) 2
        (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M) g α
          (laplacianDomainPow_succ_subset_laplacianDomain
            (I := I) (M := M) g 1 hu_h)).fChart
        (chartTargetEuclid (I := I) (M := M) α)
      rw [Nat.sub_zero]
      exact base_f_chart_memWkp_m
        (I := I) (M := M) g α m
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)
        h_chart_H_m_plus_1_u h_chart_H_m_RHS
    fChartEffective_ae_zero_off_K := by
      change (chartBilinearH1ComplDataOfLaplacianDomain (I := I) (M := M)
        g α (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)).fChart =ᵐ[
        (_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
          (chartTargetEuclid (I := I) (M := M) α \
            chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ))
      have h_ae := base_f_chart_ae_zero_off_chart_image_pou_tsupport (I := I) (M := M) g α
        (laplacianDomainPow_succ_subset_laplacianDomain
          (I := I) (M := M) g 1 hu_h)
      filter_upwards [h_ae] with y hy using hy }

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.buildLevelZero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.buildLevelZero target :: scope.openDecls } }

private def buildLevelStep
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    {hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2}
    {m j : ℕ} (hj_succ_le : j + 1 ≤ m)
    {n : ℕ} (dirs : Fin n → Fin (Module.finrank ℝ E))
    (B_j : LevelBundle (I := I) (M := M) g α dirs hu_h m j)
    (h_chart_H_m_plus_1_u :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α)) :
    LevelBundle (I := I) (M := M) g α dirs hu_h m (j + 1) := by
  classical
  have h_chart_H_j_plus_1 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (j + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_chart_H_m_plus_1_u.le_of_le (by omega : j + 1 ≤ m + 1)
  have h_chart_H_j_plus_2 :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (j + 2) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_chart_H_m_plus_1_u.le_of_le (by omega : j + 2 ≤ m + 1)
  have h_D_j_W1p : DeGiorgi.MemW1p (d := Module.finrank ℝ E) 2 B_j.data.diffChartForcing
      (chartTargetEuclid (I := I) (M := M) α) := by
    have h_le_1 : (1 : ℕ) ≤ m - j := by omega
    have h_w1p_eq : DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 1 2 B_j.data.diffChartForcing
        (chartTargetEuclid (I := I) (M := M) α) :=
      B_j.fChartEffective_memWkp.le_of_le h_le_1
    rw [DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp.one_iff_memW1p]
      at h_w1p_eq
    exact h_w1p_eq
  let D_next : IteratedDiffChartBilinearData (I := I) (M := M) g α u_h (j + 1) :=
    iteratedDiffChartBilinearDataStep (I := I) (M := M) g α
      (u_h := u_h) j B_j.data (padDirs dirs j)
      h_chart_H_j_plus_1 h_chart_H_j_plus_2
      h_D_j_W1p B_j.fChartEffective_ae_zero_off_K
  have h_directions_eq : D_next.directions = dirsOf dirs (j + 1) := by
    change Fin.snoc B_j.data.directions (padDirs dirs j) = dirsOf dirs (j + 1)
    rw [dirsOf_succ, B_j.directions_eq]
  set K_next : ℕ := m - j - 1 with hK_next_def
  have hK_succ_eq : K_next + 1 = m - j := by omega
  have hK_next_chart_eq : j + 2 + K_next = m + 1 := by omega
  have h_prev_memWkp_succ :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (K_next + 1) 2 B_j.data.diffChartForcing
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hK_succ_eq]; exact B_j.fChartEffective_memWkp
  have h_chart_H_propagator :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (j + 2 + K_next) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [hK_next_chart_eq]; exact h_chart_H_m_plus_1_u
  have h_next_memWkp_K :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) K_next 2
        (fChartEffectiveStep (I := I) (M := M) g α u_h j B_j.data.directions
          B_j.data.diffChartForcing (padDirs dirs j))
        (chartTargetEuclid (I := I) (M := M) α) :=
    fChartEffectiveStep_memWkp_K_two (I := I) (M := M) g α u_h j K_next
      B_j.data.directions B_j.data.diffChartForcing (padDirs dirs j)
      h_prev_memWkp_succ B_j.fChartEffective_ae_zero_off_K h_chart_H_propagator
  have h_next_fChartEffective_eq : D_next.diffChartForcing =
      fChartEffectiveStep (I := I) (M := M) g α u_h j B_j.data.directions
        B_j.data.diffChartForcing (padDirs dirs j) := rfl
  have h_D_next_memWkp :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m - (j + 1)) 2 D_next.diffChartForcing
        (chartTargetEuclid (I := I) (M := M) α) := by
    rw [h_next_fChartEffective_eq]
    have h_eq : K_next = m - (j + 1) := by omega
    rw [← h_eq]
    exact h_next_memWkp_K
  have h_D_next_ae_zero :
      D_next.diffChartForcing =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α)]
        (fun _ : EuclN => (0 : ℝ)) := by
    rw [h_next_fChartEffective_eq]
    have h_diff_open : IsOpen
        (chartTargetEuclid (I := I) (M := M) α \
          chartImagePOUTsupport (I := I) (M := M) α) :=
      (chartTargetEuclid_isOpen (I := I) (M := M) α).sdiff
        (chartImagePOUTsupport_isCompact (I := I) (M := M) α).isClosed
    refine (_root_.MeasureTheory.ae_restrict_iff' h_diff_open.measurableSet).mpr ?_
    refine Filter.Eventually.of_forall ?_
    intro y hy
    unfold fChartEffectiveStep
    exact Set.indicator_of_notMem hy.2 _
  exact
    { data := D_next
      directions_eq := h_directions_eq
      fChartEffective_memWkp := h_D_next_memWkp
      fChartEffective_ae_zero_off_K := h_D_next_ae_zero }

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.buildLevelStep
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.buildLevelStep target :: scope.openDecls } }

private def buildLevel
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (m : ℕ)
    {n : ℕ} (dirs : Fin n → Fin (Module.finrank ℝ E))
    (h_chart_H_m_plus_1_u :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) (m + 1) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    (h_chart_H_m_RHS :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) m 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    (j : ℕ) (hj : j ≤ m) :
    LevelBundle (I := I) (M := M) g α dirs hu_h m j := by
  induction j with
  | zero =>
      exact buildLevelZero (I := I) (M := M) g α hu_h m dirs
        h_chart_H_m_plus_1_u h_chart_H_m_RHS
  | succ j ih =>
      have hj_le : j ≤ m := Nat.le_of_succ_le hj
      have hj_succ_le : j + 1 ≤ m := hj
      let B_j := ih hj_le
      exact buildLevelStep (I := I) (M := M) g α
        (hu_h := hu_h) (m := m) (j := j) hj_succ_le dirs B_j (h_chart_H_m_plus_1_u α)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.buildLevel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.buildLevel target :: scope.openDecls } }

private theorem chosenMthMixed_memWkp_two_two
    (g : SmoothRiemannianMetric I M) (α : M)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (m : ℕ)
    (h_chart_H_m_plus_1_u :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) (m + 1) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    (h_chart_H_m_RHS :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) m 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    (dirs : Fin m → Fin (Module.finrank ℝ E)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) 2 2
      (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  let B_m : LevelBundle (I := I) (M := M) g α dirs hu_h m m :=
    buildLevel (I := I) (M := M) g α hu_h m dirs
      h_chart_H_m_plus_1_u h_chart_H_m_RHS m (le_refl _)
  have h_directions : B_m.data.directions = dirs := by
    rw [B_m.directions_eq, dirsOf_self]
  have h_chart_H_m_plus_1_at_α :=
    h_chart_H_m_plus_1_u α
  obtain ⟨Ω'', hΩ''_open, hKα_in_Ω'', hΩ''_compact_closure,
      h_closureΩ''_in_chart, h_memWkp_22_Ω''⟩ :=
    iteratedDerivedChartBilinear_memWkp_two_two_interior_weakened
      (I := I) (M := M) g α m B_m.data h_chart_H_m_plus_1_at_α
  rw [h_directions] at h_memWkp_22_Ω''
  set Ω : Set EuclN := chartTargetEuclid (I := I) (M := M) α with hΩ_def
  set Kα : Set EuclN := chartImagePOUTsupport (I := I) (M := M) α with hKα_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hKα_compact : IsCompact Kα :=
    chartImagePOUTsupport_isCompact (I := I) (M := M) α
  have hKα_in_Ω : Kα ⊆ Ω :=
    chartImagePOUTsupport_subset_target (I := I) (M := M) α
  have hΩ''_in_Ω : Ω'' ⊆ Ω := fun y hy => h_closureΩ''_in_chart (subset_closure hy)
  have h_parent_m :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) m 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        Ω :=
    h_chart_H_m_plus_1_at_α.le_of_le (by omega : m ≤ m + 1)
  have h_chosen_ae_zero :
      chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m dirs
        =ᵐ[(_root_.MeasureTheory.MeasureSpace.volume : _root_.MeasureTheory.Measure EuclN).restrict (Ω \ Kα)]
        (fun _ : EuclN => (0 : ℝ)) :=
    chosenMthMixed_ae_zero_off_Kα (I := I) (M := M) g α u_h m h_parent_m dirs
  exact MemWkp.extend_of_ae_zero_outside_compact (E := E) 2
    hΩ_open hΩ''_open hΩ''_in_Ω hKα_compact hKα_in_Ω''
    h_memWkp_22_Ω'' h_chosen_ae_zero

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.chosenMthMixed_memWkp_two_two
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.chosenMthMixed_memWkp_two_two target :: scope.openDecls } }

theorem chartPushed_memWkp_succ_jump
    (g : SmoothRiemannianMetric I M) (α : M) (m : ℕ)
    {u_h : H1Compl (I := I) (M := M) g}
    (hu_h : u_h ∈ laplacianDomainPow (I := I) (M := M) g 2)
    (h_chart_H_m_plus_1_u :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) (m + 1) 2
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
    (h_chart_H_m_RHS :
      DifferentialGeometry.Analysis.Sobolev.Chart.MemWkpChart
        (I := I) (M := M) m 2
        ((laplacianDomain.preimage (I := I) (M := M) g
            ⟨u_h, laplacianDomainPow_succ_subset_laplacianDomain
              (I := I) (M := M) g 1 hu_h⟩ :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ)) :
    DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
      (d := Module.finrank ℝ E) (m + 2) 2
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushed
        (I := I) (M := M) (chartAtlasPOU I M) α
        ((H1ComplToLp (I := I) (M := M) g u_h :
          Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
      (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I) (M := M) α) := by
  classical
  have h_top_memWkp_two : ∀ (idx : Fin m → Fin (Module.finrank ℝ E)),
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) 2 2
        (chosenMthMixedPartialChartPushedU (I := I) (M := M) g α u_h m idx)
        (chartTargetEuclid (I := I) (M := M) α) := fun idx =>
    chosenMthMixed_memWkp_two_two (I := I) (M := M) g α hu_h m
      h_chart_H_m_plus_1_u h_chart_H_m_RHS idx
  have h_chart_H_m_plus_1_at_α :
      DifferentialGeometry.Analysis.Sobolev.Euclidean.MemWkp
        (d := Module.finrank ℝ E) (m + 1) 2
        (chartPushed (I := I) (M := M) (chartAtlasPOU I M) α
          ((H1ComplToLp (I := I) (M := M) g u_h :
            Lp ℝ 2 (riemannianVolumeMeasure (I := I) (M := M) g)) : M → ℝ))
        (chartTargetEuclid (I := I) (M := M) α) :=
    h_chart_H_m_plus_1_u α
  exact chartPushed_memWkp_m_plus_two_step (I := I) (M := M) g α u_h m
    h_chart_H_m_plus_1_at_α h_top_memWkp_two

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.chartPushed_memWkp_succ_jump then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.chartPushed_memWkp_succ_jump"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.chartPushed_memWkp_succ_jump ``Submission.DifferentialGeometry.Analysis.Laplacian.IteratedChartHmJump.chartPushed_memWkp_succ_jump

end IteratedChartHmJump
end Laplacian
end Analysis
end DifferentialGeometry

end
