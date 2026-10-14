import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.IntrinsicTimeJetConvergence
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.TimeJets
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCap
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.OpenRestriction
import Submission.DifferentialGeometry.Topology.SigmaCompactOpen

import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.GeometricCutoff
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RecenterAux
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ShrinkingCylinderIsometries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section

open _root_.Set _root_.Submission.Set _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp [ThreeSpace]⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instFactEqNatFinrankRealThreeSpaceHAddOfNat target :: scope.openDecls } }

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instNeZeroNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) :=
  ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instNeZeroNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.instNeZeroNatFinrankRealProdEuclideanSpaceFinOfNat_differentialGeometry target :: scope.openDecls } }

private theorem shrinkingCylinderMetric_isSolutionOn_neckBuffer_closed
    (δ a : ℝ) (ha : a ≤ 0) :
    IsSolutionOn ({ base.metric := fun t =>
      (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen (neckBuffer δ) } :
      SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ)
        (RealTimeInterval.closed a 0 ha)) := by
  let : SigmaCompactSpace (neckBuffer δ) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen NeckCylinderModel
      (neckBuffer δ).isOpen)
  have hcyl := PDE.RicciFlow.shrinkingCylinderMetric_isSolutionOn_interval
    (E := ThreeSpace) (by linarith : a < 1) (le_refl (1 : ℝ))
  have htime := isSolutionOn_timeRestrict
    (D' := RealTimeInterval.closed a 0 ha) hcyl
    (fun t ht => ⟨ht.1, by linarith [ht.2]⟩)
    (fun t ht => ⟨ht.1, by linarith [ht.2]⟩)
  exact isSolutionOn_restrictOpen _ htime (neckBuffer δ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.shrinkingCylinderMetric_isSolutionOn_neckBuffer_closed
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.shrinkingCylinderMetric_isSolutionOn_neckBuffer_closed target :: scope.openDecls } }

theorem exists_neckBuffer_metric_difference_time_jets_on_Icc_of_spatial_convergence
    {δ a c : ℝ} {D : RealTimeInterval} (hac : a < c) (hc0 : c < 0)
    (S : ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ) D)
    (hS : ∀ n, IsSolutionOn (S n))
    (hcarrier : _root_.Set.Icc a 0 ⊆ D.carrier) (hregular : _root_.Set.Ioo a 0 ⊆ D.regular)
    (hconv : ∀ K : Set (neckBuffer δ), IsCompact K → ∀ r : ℕ,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc c 0,
        metricDerivNormSupOn K r ((S n).base.metric t)
          ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen (neckBuffer δ))
          (roundCylinderMetric.restrictOpen (neckBuffer δ)) < ε) :
    ∃ Z : ℕ → ℕ → ℝ → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2,
      (∀ n q t, t ∈ _root_.Set.Icc c 0 → ∀ x,
        Z n q t x = iteratedDerivWithin q
          (fun s => metricTensorField ((S n).base.metric s) x -
            metricTensorField
              ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) s).restrictOpen
                (neckBuffer δ)) x) (_root_.Set.Icc c 0) t) ∧
      (∀ n q t, t ∈ _root_.Set.Icc c 0 → ∀ x,
        HasDerivWithinAt (fun s => Z n q s x) (Z n (q + 1) t x) (_root_.Set.Icc c 0) t) ∧
      ∀ K : Set (neckBuffer δ), IsCompact K → ∀ k : ℕ, ∀ η : ℝ, 0 < η →
        ∃ N : ℕ, ∀ n ≥ N, ∀ r q : ℕ, r + 2 * q ≤ k →
          ∀ t ∈ _root_.Set.Icc c 0, ∀ x ∈ K,
            tensor02CovDerivNormWith r (Z n q t)
              ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
                (neckBuffer δ))
              ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
                (neckBuffer δ)) x ≤ η := by
  classical
  let : SigmaCompactSpace (neckBuffer δ) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen NeckCylinderModel
      (neckBuffer δ).isOpen)
  have ha0 : a ≤ 0 := hac.le.trans hc0.le
  let D₀ := RealTimeInterval.closed a 0 ha0
  let U : ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ) D₀ :=
    fun n => (S n).timeRestrict D₀
  have hU (n : ℕ) : IsSolutionOn (U n) :=
    isSolutionOn_timeRestrict (hS n) hcarrier hregular
  let C : SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ) D₀ :=
    { base.metric := fun t =>
        (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen (neckBuffer δ) }
  have hC : IsSolutionOn C := shrinkingCylinderMetric_isSolutionOn_neckBuffer_closed δ a ha0
  choose B hBzero hB using (fun n =>
    Perelman.KappaSolutions.exists_ordinary_metric_time_jets_on_closed_interval
      (U n) (hU n) hac hc0 rfl Subset.rfl)
  obtain ⟨A, hAzero, hA⟩ :=
    Perelman.KappaSolutions.exists_ordinary_metric_time_jets_on_closed_interval
      C hC hac hc0 rfl Subset.rfl
  let Z : ℕ → ℕ → ℝ → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2 :=
    fun n q t => B n q t - A q t
  have hZ (n q : ℕ) (t : ℝ) (ht : t ∈ _root_.Set.Icc c 0) (x : neckBuffer δ) :
      HasDerivWithinAt (fun s => Z n q s x) (Z n (q + 1) t x) (_root_.Set.Icc c 0) t :=
    (hB n q t ht x).2.sub (hA q t ht x).2
  refine ⟨Z, ?_, hZ, ?_⟩
  · intro n q t ht x
    apply (DifferentialGeometry.Analysis.iteratedDerivWithin_eq_of_hasDerivWithinAt
      (uniqueDiffOn_Icc hc0) _ (fun q t => Z n q t x)
      (fun q t ht => hZ n q t ht x) ?_ q ht).symm
    intro s _hs
    change _ = B n 0 s x - A 0 s x
    rw [hBzero, hAzero]
    rfl
  · intro K hK k η hη
    have hbound (r q : ℕ) : ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc c 0, ∀ x ∈ K,
        tensor02CovDerivNormWith r (Z n q t) (C.base.metric t) (C.base.metric t) x ≤ η :=
      Perelman.KappaSolutions.metric_time_jet_errors_uniform_on_compacts_of_closed_interval
        U hU C hC hac hc0 rfl Subset.rfl
        (roundCylinderMetric.restrictOpen (neckBuffer δ)) hconv B A hBzero hAzero
        (fun n q t ht x => (hB n q t ht x).2) (fun q t ht x => (hA q t ht x).2)
        hK r q η hη
    choose N hN using hbound
    refine ⟨(Finset.range (k + 1)).sup (fun r =>
      (Finset.range (k + 1)).sup (N r)), ?_⟩
    intro n hn r q hrq t ht x hx
    apply hN r q n ?_ t ht x hx
    refine le_trans ?_ hn
    exact le_trans
      (Finset.le_sup (f := N r) (Finset.mem_range.mpr (by omega)))
      (Finset.le_sup (f := fun r => (Finset.range (k + 1)).sup (N r))
        (Finset.mem_range.mpr (by omega)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckBuffer_metric_difference_time_jets_on_Icc_of_spatial_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckBuffer_metric_difference_time_jets_on_Icc_of_spatial_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckBuffer_metric_difference_time_jets_on_Icc_of_spatial_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckBuffer_metric_difference_time_jets_on_Icc_of_spatial_convergence

theorem exists_neckBuffer_metric_difference_time_jets_of_spatial_convergence
    {δ a : ℝ} {D : RealTimeInterval} (ha : a < -1)
    (S : ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ) D)
    (hS : ∀ n, IsSolutionOn (S n))
    (hcarrier : _root_.Set.Icc a 0 ⊆ D.carrier) (hregular : _root_.Set.Ioo a 0 ⊆ D.regular)
    (hconv : ∀ K : Set (neckBuffer δ), IsCompact K → ∀ r : ℕ,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc (-1 : ℝ) 0,
        metricDerivNormSupOn K r ((S n).base.metric t)
          ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen (neckBuffer δ))
          (roundCylinderMetric.restrictOpen (neckBuffer δ)) < ε) :
    ∃ Z : ℕ → ℕ → ℝ → Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2,
      (∀ n q t, t ∈ _root_.Set.Icc (-1 : ℝ) 0 → ∀ x,
        Z n q t x = iteratedDerivWithin q
          (fun s => metricTensorField ((S n).base.metric s) x -
            metricTensorField
              ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) s).restrictOpen
                (neckBuffer δ)) x) (_root_.Set.Icc (-1 : ℝ) 0) t) ∧
      (∀ n q t, t ∈ _root_.Set.Icc (-1 : ℝ) 0 → ∀ x,
        HasDerivWithinAt (fun s => Z n q s x) (Z n (q + 1) t x) (_root_.Set.Icc (-1 : ℝ) 0) t) ∧
      ∀ K : Set (neckBuffer δ), IsCompact K → ∀ k : ℕ, ∀ η : ℝ, 0 < η →
        ∃ N : ℕ, ∀ n ≥ N, ∀ r q : ℕ, r + 2 * q ≤ k →
          ∀ t ∈ _root_.Set.Icc (-1 : ℝ) 0, ∀ x ∈ K,
            tensor02CovDerivNormWith r (Z n q t)
              ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
                (neckBuffer δ))
              ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen
                (neckBuffer δ)) x ≤ η := by
  exact exists_neckBuffer_metric_difference_time_jets_on_Icc_of_spatial_convergence
    ha (by norm_num) S hS hcarrier hregular hconv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckBuffer_metric_difference_time_jets_of_spatial_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckBuffer_metric_difference_time_jets_of_spatial_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckBuffer_metric_difference_time_jets_of_spatial_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.exists_neckBuffer_metric_difference_time_jets_of_spatial_convergence

theorem eventually_exists_neck_time_difference_jets_on_Icc_of_spatial_convergence
    {δ a c : ℝ} {D : RealTimeInterval} (hδ : 0 < δ) (hac : a < c) (hc0 : c < 0) (k : ℕ)
    (S : ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ) D)
    (hS : ∀ n, IsSolutionOn (S n))
    (hcarrier : _root_.Set.Icc a 0 ⊆ D.carrier) (hregular : _root_.Set.Ioo a 0 ⊆ D.regular)
    (hconv : ∀ K : Set (neckBuffer δ), IsCompact K → ∀ r : ℕ,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc c 0,
        metricDerivNormSupOn K r ((S n).base.metric t)
          ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen (neckBuffer δ))
          (roundCylinderMetric.restrictOpen (neckBuffer δ)) < ε) :
    ∀ᶠ n in _root_.Filter.atTop,
      ∃ Z : (b : ℕ) → _root_.Set.Icc c 0 →
        Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2,
        (∀ b v x, Z b v x = iteratedDerivWithin b (fun t =>
          metricTensorField ((S n).base.metric t) x -
            metricTensorField ((shrinkingCylinderMetric
              ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
                (neckBuffer δ)) x) (_root_.Set.Icc c 0) v.1) ∧
        ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ k →
          ∀ v : _root_.Set.Icc c 0, ∀ x ∈ neckClosedTest δ,
            let g := (shrinkingCylinderMetric
              ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
            Real.sqrt (normSq0S g x (r + 2)
              (cylinderTensorCovDeriv g (Z q v) r x)) ≤ η := by
  obtain ⟨Z, hZ, _, hbound⟩ :=
    exists_neckBuffer_metric_difference_time_jets_on_Icc_of_spatial_convergence
      hac hc0 S hS hcarrier hregular hconv
  obtain ⟨N, hN⟩ := hbound (neckClosedTest δ) (isCompact_neckClosedTest δ) k (δ / 2)
    (half_pos hδ)
  filter_upwards [_root_.Filter.eventually_ge_atTop N] with n hn
  refine ⟨fun b v => Z n b v.1, ?_, δ / 2, half_lt_self hδ, ?_⟩
  · intro b v x
    rw [hZ n b v.1 v.2 x]
    apply iteratedDerivWithin_congr _ v.2
    intro t ht
    simp only [shrinkingCylinderMetric_eq_flow, min_eq_left ht.2]
  · intro r q hrq v x hx
    have hh := hN n hn r q hrq v.1 v.2 x hx
    simp only [cylinderTensorCovDeriv_eq_tensor02CovDeriv]
    change tensor02CovDerivNormWith r (Z n q v.1)
      ((shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ))
      ((shrinkingCylinderMetric ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen
        (neckBuffer δ)) x ≤ δ / 2
    simpa only [shrinkingCylinderMetric_eq_flow] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.eventually_exists_neck_time_difference_jets_on_Icc_of_spatial_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.eventually_exists_neck_time_difference_jets_on_Icc_of_spatial_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.eventually_exists_neck_time_difference_jets_on_Icc_of_spatial_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.eventually_exists_neck_time_difference_jets_on_Icc_of_spatial_convergence

theorem eventually_exists_neck_time_difference_jets_of_spatial_convergence
    {δ a : ℝ} {D : RealTimeInterval} (hδ : 0 < δ) (ha : a < -1) (k : ℕ)
    (S : ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ) D)
    (hS : ∀ n, IsSolutionOn (S n))
    (hcarrier : _root_.Set.Icc a 0 ⊆ D.carrier) (hregular : _root_.Set.Ioo a 0 ⊆ D.regular)
    (hconv : ∀ K : Set (neckBuffer δ), IsCompact K → ∀ r : ℕ,
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ _root_.Set.Icc (-1 : ℝ) 0,
        metricDerivNormSupOn K r ((S n).base.metric t)
          ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) t).restrictOpen (neckBuffer δ))
          (roundCylinderMetric.restrictOpen (neckBuffer δ)) < ε) :
    ∀ᶠ n in _root_.Filter.atTop,
      ∃ Z : (b : ℕ) → _root_.Set.Icc (-1 : ℝ) 0 →
        Tensor0SField (I := NeckCylinderModel) (M := neckBuffer δ) ∞ 2,
        (∀ b v x, Z b v x = iteratedDerivWithin b (fun t =>
          metricTensorField ((S n).base.metric t) x -
            metricTensorField ((shrinkingCylinderMetric
              ⟨min t 0, (min_le_right t 0).trans_lt zero_lt_one⟩).restrictOpen
                (neckBuffer δ)) x) (_root_.Set.Icc (-1 : ℝ) 0) v.1) ∧
        ∃ η : ℝ, η < δ ∧ ∀ r q : ℕ, r + 2 * q ≤ k →
          ∀ v : _root_.Set.Icc (-1 : ℝ) 0, ∀ x ∈ neckClosedTest δ,
            let g := (shrinkingCylinderMetric
              ⟨v.1, v.2.2.trans_lt zero_lt_one⟩).restrictOpen (neckBuffer δ)
            Real.sqrt (normSq0S g x (r + 2)
              (cylinderTensorCovDeriv g (Z q v) r x)) ≤ η := by
  exact eventually_exists_neck_time_difference_jets_on_Icc_of_spatial_convergence
    hδ ha (by norm_num) k S hS hcarrier hregular hconv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.eventually_exists_neck_time_difference_jets_of_spatial_convergence then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.eventually_exists_neck_time_difference_jets_of_spatial_convergence"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.eventually_exists_neck_time_difference_jets_of_spatial_convergence ``Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.eventually_exists_neck_time_difference_jets_of_spatial_convergence

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
