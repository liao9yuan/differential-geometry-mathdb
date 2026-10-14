import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.LocalMinimality
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.MinimizerEquation
import Submission.DifferentialGeometry.Geometry.Exponential.Variation.Jacobi
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Chart.CarrierLocalMinimality

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [CompactSpace M] in
theorem lRegularizedAction_minimizer_acceleration_eq_on_chart_piece_interior
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (ht : StrictMono t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i, _root_.Set.MapsTo gamma
      (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, _root_.Set.EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)))
    (hreg : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ D.regular)
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T delta a b) :
    ∀ (i : Fin m) (s : Real), s ∈ _root_.Set.Ioo (t i.castSucc) (t i.succ) →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          gamma (fun q ↦ lVelocity (I := I) gamma q) s =
        lRegularizedAccel S T s (gamma s) (lVelocity (I := I) gamma s) := by
  classical
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  intro i s hs
  have hpos : t i.castSucc < t i.succ := ht Fin.castSucc_lt_succ
  have hL : 0 < partitionIntervalLength t i := by
    simpa only [partitionIntervalLength] using sub_pos.mpr hpos
  have hleft : a ≤ t i.castSucc := by
    rw [← ht0]
    exact ht.monotone (Fin.zero_le _)
  have hright : t i.succ ≤ b := by
    rw [← htlast]
    exact ht.monotone (Fin.le_last _)
  have hshift : _root_.Set.MapsTo (fun r : Real ↦ t i.castSucc + r)
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i))
      (_root_.Set.Icc (t i.castSucc) (t i.succ)) := by
    intro r hr
    change r ∈ _root_.Set.Icc (0 : Real) (t i.succ - t i.castSucc) at hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hregi : ∀ r ∈ _root_.Set.Icc (0 : Real) (partitionIntervalLength t i),
      T - (t i.castSucc + r) ^ 2 ∈ D.regular := by
    intro r hr
    exact hreg (t i.castSucc + r)
      ⟨hleft.trans (hshift hr).1, (hshift hr).2.trans hright⟩
  have hchart : _root_.Set.MapsTo (u i).toFun (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i))
      (interior (extChartAt I (p i)).target) := by
    rw [(isOpen_extChartAt_target (I := I) (p i)).interior_eq]
    intro r hr
    rw [hrep i hr]
    exact (extChartAt I (p i)).map_source (by
      simpa only [extChartAt_source] using hsrc i (hshift hr))
  have hlocal : IsLocalMinOn
      (lChartAction S T (t i.castSucc) (p i))
      (sameTimeEnds (u i)) (u i) :=
    lChartAction_isLocalMinOn_of_lRegularizedAction_minimizer S hS.smoothMetric hSc T a b t ht.monotone
      ht0 htlast p gamma hgamma u hsrc hrep hreg hmin i hpos
  let r : Real := s - t i.castSucc
  have hr : r ∈ _root_.Set.Ioo (0 : Real) (partitionIntervalLength t i) := by
    dsimp only [r, partitionIntervalLength]
    constructor <;> linarith [hs.1, hs.2]
  let alpha : Real → M := fun q ↦
    (extChartAt I (p i)).symm ((u i).toFun (q - t i.castSucc))
  have hacc := lChartAction_minimizer_acceleration_eq (I := I) S hS T (t i.castSucc)
    (p i) hL (u i) hregi hchart hlocal r hr
  have hsadd : t i.castSucc + r = s := by
    dsimp only [r]
    ring
  have heqOn : _root_.Set.EqOn gamma alpha (_root_.Set.Ioo (t i.castSucc) (t i.succ)) := by
    intro q hq
    have hqr : q - t i.castSucc ∈ _root_.Set.Icc (0 : Real) (partitionIntervalLength t i) := by
      dsimp only [partitionIntervalLength]
      constructor <;> linarith [hq.1, hq.2]
    have hqsrc : gamma q ∈ (extChartAt I (p i)).source := by
      simpa only [extChartAt_source] using
        hsrc i ⟨hq.1.le, hq.2.le⟩
    have hinv := (extChartAt I (p i)).left_inv hqsrc
    dsimp only [alpha]
    rw [hrep i hqr]
    have hsum : t i.castSucc + (q - t i.castSucc) = q := by ring
    simpa only [hsum] using hinv.symm
  have heq : gamma =ᶠ[nhds s] alpha :=
    heqOn.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
  have hvel : ∀ᶠ q in nhds s,
      (lVelocity (I := I) gamma q : E) =
        (lVelocity (I := I) alpha q : E) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with q hq
    have hqeq : gamma =ᶠ[nhds q] alpha :=
      heqOn.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hq)
    exact congrArg (fun L : Real →L[Real] E ↦ L (1 : Real))
      (Filter.EventuallyEq.mfderiv_eq
        (I := modelWithCornersSelf Real Real) (I' := I) hqeq)
  have hcov :=
    DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
      (I := I) (S.base.metric (T - s ^ 2))
      (fun q ↦ lVelocity (I := I) gamma q)
      (fun q ↦ lVelocity (I := I) alpha q) heq hvel
  change
    (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
        (fun q ↦ lVelocity (I := I) gamma q) s : E) =
      (lRegularizedAccel S T s (gamma s) (lVelocity (I := I) gamma s) : E)
  rw [hcov, heq.self_of_nhds, hvel.self_of_nhds, ← hsadd]
  exact congrArg (fun v : TangentSpace I (alpha (t i.castSucc + r)) ↦ (v : E)) hacc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimizer_acceleration_eq_on_chart_piece_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimizer_acceleration_eq_on_chart_piece_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimizer_acceleration_eq_on_chart_piece_interior ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimizer_acceleration_eq_on_chart_piece_interior

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open scoped _root_.ContDiff _root_.Manifold _root_.Submission.Manifold _root_.Topology _root_.Submission.Topology

open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}
omit [CompactSpace M] in
theorem lRegularizedAction_minimizer_acceleration_eq_on_chart_piece_interior_of_spatial_derivatives
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S)
    (T a b : Real) {m : Nat} (t : Fin (m + 1) → Real)
    (ht : StrictMono t) (ht0 : t 0 = a)
    (htlast : t (Fin.last m) = b)
    (p : Fin m → M) (gamma : Real → M) (hgamma : Continuous gamma)
    (u : (i : Fin m) → timeH1 E (partitionIntervalLength t i))
    (hsrc : ∀ i, _root_.Set.MapsTo gamma
      (_root_.Set.Icc (t i.castSucc) (t i.succ)) (chartAt H (p i)).source)
    (hrep : ∀ i, _root_.Set.EqOn (u i).toFun
      (fun r ↦ extChartAt I (p i) (gamma (t i.castSucc + r)))
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i)))
    (J : Set Real) (hJ : J ⊆ D.carrier)
    (htime : ∀ s ∈ _root_.Set.Icc a b, T - s ^ 2 ∈ J)
    (hreg : ∀ s ∈ _root_.Set.Ioo a b, T - s ^ 2 ∈ D.regular)
    (hGramFd : ∀ i, ContinuousOn (fun z : Real × E => fderiv Real
      (fun y : E => chartGramOp (I := I) S.family (p i) (z.1, y)) z.2)
      (J ×ˢ interior (extChartAt I (p i)).target))
    (hScalFd : ∀ i, ContinuousOn (fun z : Real × E => fderiv Real
      (DifferentialGeometry.Tensor.Coordinates.scalarOnE (I := I) (p i) (S.scalar z.1)) z.2)
      (J ×ˢ interior (extChartAt I (p i)).target))
    (hmin : ∀ delta : Real → M,
      ContMDiff (modelWithCornersSelf Real Real) I 1 delta →
      delta a = gamma a → delta b = gamma b →
      lRegularizedAction S T gamma a b ≤ lRegularizedAction S T delta a b)
    (i : Fin m) (s : Real) (hs : s ∈ _root_.Set.Ioo (t i.castSucc) (t i.succ)) :
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          gamma (fun q ↦ lVelocity (I := I) gamma q) s =
        lRegularizedAccel S T s (gamma s) (lVelocity (I := I) gamma s) := by
  classical
  let hSc : ScalarSTContOn (I := I) (M := M) S := ⟨hS.scalarCont⟩
  have hpos : t i.castSucc < t i.succ :=
    ht Fin.castSucc_lt_succ
  have hL : 0 < partitionIntervalLength t i := by
    simpa only [partitionIntervalLength] using sub_pos.mpr hpos
  have hleft : a ≤ t i.castSucc := by
    rw [← ht0]
    exact ht.monotone (Fin.zero_le _)
  have hright : t i.succ ≤ b := by
    rw [← htlast]
    exact ht.monotone (Fin.le_last _)
  have hshift : _root_.Set.MapsTo (fun r : Real ↦ t i.castSucc + r)
      (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i))
      (_root_.Set.Icc (t i.castSucc) (t i.succ)) := by
    intro r hr
    change r ∈ _root_.Set.Icc (0 : Real) (t i.succ - t i.castSucc) at hr
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have htimei : ∀ r ∈ _root_.Set.Icc (0 : Real) (partitionIntervalLength t i),
      T - (t i.castSucc + r) ^ 2 ∈ J := by
    intro r hr
    exact htime (t i.castSucc + r)
      ⟨hleft.trans (hshift hr).1, (hshift hr).2.trans hright⟩
  have hregi : ∀ r ∈ _root_.Set.Ioo (0 : Real) (partitionIntervalLength t i),
      T - (t i.castSucc + r) ^ 2 ∈ D.regular := by
    intro r hr
    apply hreg
    change r ∈ _root_.Set.Ioo (0 : Real) (t i.succ - t i.castSucc) at hr
    constructor <;> linarith [hr.1, hr.2]
  have hchart : _root_.Set.MapsTo (u i).toFun (_root_.Set.Icc (0 : Real) (partitionIntervalLength t i))
      (interior (extChartAt I (p i)).target) := by
    rw [(isOpen_extChartAt_target (I := I) (p i)).interior_eq]
    intro r hr
    rw [hrep i hr]
    exact (extChartAt I (p i)).map_source (by
      simpa only [extChartAt_source] using hsrc i (hshift hr))
  have hlocal : IsLocalMinOn
      (lChartAction S T (t i.castSucc) (p i))
      (sameTimeEnds (u i)) (u i) :=
    lChartAction_isLocalMinOn_of_lRegularizedAction_minimizer_of_carrier S hS.smoothMetric hSc T a b t ht.monotone
      ht0 htlast p gamma hgamma u hsrc hrep (fun s hs => hJ (htime s hs)) hmin i hpos
  let r : Real := s - t i.castSucc
  have hr : r ∈ _root_.Set.Ioo (0 : Real) (partitionIntervalLength t i) := by
    dsimp only [r, partitionIntervalLength]
    constructor <;> linarith [hs.1, hs.2]
  let alpha : Real → M := fun q ↦
    (extChartAt I (p i)).symm ((u i).toFun (q - t i.castSucc))
  have hacc := lChartAction_minimizer_acceleration_eq_of_spatial_derivatives (I := I) S hS T (t i.castSucc)
    (p i) hL (u i) hJ htimei hregi (hGramFd i) (hScalFd i) hchart hlocal r hr
  have hsadd : t i.castSucc + r = s := by
    dsimp only [r]
    ring
  have heqOn : _root_.Set.EqOn gamma alpha (_root_.Set.Ioo (t i.castSucc) (t i.succ)) := by
    intro q hq
    have hqr : q - t i.castSucc ∈ _root_.Set.Icc (0 : Real) (partitionIntervalLength t i) := by
      dsimp only [partitionIntervalLength]
      constructor <;> linarith [hq.1, hq.2]
    have hqsrc : gamma q ∈ (extChartAt I (p i)).source := by
      simpa only [extChartAt_source] using
        hsrc i ⟨hq.1.le, hq.2.le⟩
    have hinv := (extChartAt I (p i)).left_inv hqsrc
    dsimp only [alpha]
    rw [hrep i hqr]
    have hsum : t i.castSucc + (q - t i.castSucc) = q := by ring
    simpa only [hsum] using hinv.symm
  have heq : gamma =ᶠ[nhds s] alpha :=
    heqOn.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
  have hvel : ∀ᶠ q in nhds s,
      (lVelocity (I := I) gamma q : E) =
        (lVelocity (I := I) alpha q : E) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with q hq
    have hqeq : gamma =ᶠ[nhds q] alpha :=
      heqOn.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hq)
    exact congrArg (fun L : Real →L[Real] E ↦ L (1 : Real))
      (Filter.EventuallyEq.mfderiv_eq
        (I := modelWithCornersSelf Real Real) (I' := I) hqeq)
  have hcov :=
    DifferentialGeometry.Geometry.Riemannian.covDerivAlong_congr_curve
      (I := I) (S.base.metric (T - s ^ 2))
      (fun q ↦ lVelocity (I := I) gamma q)
      (fun q ↦ lVelocity (I := I) alpha q) heq hvel
  change
    (covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) gamma
        (fun q ↦ lVelocity (I := I) gamma q) s : E) =
      (lRegularizedAccel S T s (gamma s) (lVelocity (I := I) gamma s) : E)
  rw [hcov, heq.self_of_nhds, hvel.self_of_nhds, ← hsadd]
  exact congrArg (fun v : TangentSpace I (alpha (t i.castSucc + r)) ↦ (v : E)) hacc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimizer_acceleration_eq_on_chart_piece_interior_of_spatial_derivatives then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimizer_acceleration_eq_on_chart_piece_interior_of_spatial_derivatives"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimizer_acceleration_eq_on_chart_piece_interior_of_spatial_derivatives ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.lRegularizedAction_minimizer_acceleration_eq_on_chart_piece_interior_of_spatial_derivatives
end DifferentialGeometry.PDE.RicciFlow.Perelman

end

end
