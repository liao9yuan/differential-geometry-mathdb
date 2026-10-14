import Submission.DifferentialGeometry.Analysis.Integration.SqrtIntegrability
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Curvature.Derivatives.Regularity.Norm
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Set _root_.MeasureTheory _root_.Filter
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem continuousOn_nablaKRm04NormSqIntrinsic_regular
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {J : Set ℝ} (hregular : J ⊆ D.regular) (k : ℕ) (x : M) :
    ContinuousOn (fun t => nablaKRm04NormSqIntrinsic S k t x) J := by
  intro t ht
  obtain ⟨a, b, hab, hsub⟩ := D.exists_Icc_regular (hregular ht)
  let Dco := RealTimeInterval.closedOpen a b (hab.1.trans hab.2)
  let Sco : SolutionOn (I := I) (M := M) Dco := S.timeRestrict Dco
  have hSco : IsSolutionOn Sco := by
    apply isSolutionOn_timeRestrict hS
    · exact fun q hq => D.regular_subset (hsub ⟨hq.1, hq.2.le⟩)
    · exact fun q hq => hsub ⟨hq.1.le, hq.2.le⟩
  have hfun : (fun q : ℝ × M => nablaKRm04NormSqIntrinsic S k q.1 q.2) =
      (fun q : ℝ × M => nablaKRm04NormSqIntrinsic Sco k q.1 q.2) := by
    funext q
    unfold nablaKRm04NormSqIntrinsic
    rw [nablaKRm04Field_eq_of_metric_eq
      (S₁ := S) (S₂ := Sco) (t₁ := q.1) (t₂ := q.1) rfl k]
    rfl
  have hc : ContinuousAt (fun q : ℝ × M => nablaKRm04NormSqIntrinsic S k q.1 q.2)
      (t, x) := by
    rw [hfun]
    exact (towerNorm_joint hSco k).continuousOn.continuousAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨hab, _root_.Set.mem_univ _⟩)
  have htx : ContinuousAt (fun s : ℝ => (s, x)) t :=
    continuousAt_id.prodMk continuousAt_const
  have htime : ContinuousAt (fun s : ℝ => nablaKRm04NormSqIntrinsic S k s x) t :=
    hc.comp (x := t) (f := fun s : ℝ => (s, x)) htx
  exact htime.continuousWithinAt

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.continuousOn_nablaKRm04NormSqIntrinsic_regular
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.continuousOn_nablaKRm04NormSqIntrinsic_regular target :: scope.openDecls } }

theorem intervalIntegrable_sqrt_nablaKRm04NormSqIntrinsic_of_sub_mul_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b A : ℝ} (hab : a ≤ b)
    (hregular : _root_.Set.Ioc a b ⊆ D.regular) (k : ℕ) (x : M)
    (hbound : ∀ t ∈ _root_.Set.Ioc a b, (t - a) * nablaKRm04NormSqIntrinsic S k t x ≤ A) :
    IntervalIntegrable (fun t => Real.sqrt (nablaKRm04NormSqIntrinsic S k t x))
      volume a b := by
  have hf := continuousOn_nablaKRm04NormSqIntrinsic_regular S hS hregular k x
  exact Analysis.intervalIntegrable_sqrt_of_sub_mul_le hab
    (hf.aestronglyMeasurable measurableSet_Ioc)
    (_root_.MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hbound)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.intervalIntegrable_sqrt_nablaKRm04NormSqIntrinsic_of_sub_mul_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.intervalIntegrable_sqrt_nablaKRm04NormSqIntrinsic_of_sub_mul_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.intervalIntegrable_sqrt_nablaKRm04NormSqIntrinsic_of_sub_mul_le ``Submission.DifferentialGeometry.PDE.RicciFlow.intervalIntegrable_sqrt_nablaKRm04NormSqIntrinsic_of_sub_mul_le

theorem integral_sqrt_nablaKRm04NormSqIntrinsic_le_of_sub_mul_le
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn S) {a b A : ℝ} (hab : a ≤ b)
    (hregular : _root_.Set.Ioc a b ⊆ D.regular) (k : ℕ) (x : M)
    (hbound : ∀ t ∈ _root_.Set.Ioc a b, (t - a) * nablaKRm04NormSqIntrinsic S k t x ≤ A) :
    (∫ t in a..b, Real.sqrt (nablaKRm04NormSqIntrinsic S k t x)) ≤
      2 * Real.sqrt A * Real.sqrt (b - a) := by
  have hf := continuousOn_nablaKRm04NormSqIntrinsic_regular S hS hregular k x
  exact Analysis.integral_sqrt_le_of_sub_mul_le hab
    (hf.aestronglyMeasurable measurableSet_Ioc)
    (_root_.MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc hbound)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.integral_sqrt_nablaKRm04NormSqIntrinsic_le_of_sub_mul_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.integral_sqrt_nablaKRm04NormSqIntrinsic_le_of_sub_mul_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.integral_sqrt_nablaKRm04NormSqIntrinsic_le_of_sub_mul_le ``Submission.DifferentialGeometry.PDE.RicciFlow.integral_sqrt_nablaKRm04NormSqIntrinsic_le_of_sub_mul_le

end DifferentialGeometry.PDE.RicciFlow

end
