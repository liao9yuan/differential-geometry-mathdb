import Submission.DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Scalar.Potential.Basic
import Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Bochner.L2
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.ScalarUniform
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.JointRegularity

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow _root_.Submission.DifferentialGeometry.Analysis.Spectral
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Entropy


open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete Real E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instCompleteSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry_1 : MeasurableSpace M := borel M

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instMeasurableSpace_differentialGeometry_1 target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry_1 : BorelSpace M := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry_1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Entropy.instBorelSpace_differentialGeometry_1 target :: scope.openDecls } }

noncomputable def conjCoeff
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    C^∞⟮I, M; Real⟯ :=
  ⟨fun x => -metricScalarAt (I := I) (M := M) (S.family.metric t) x,
    (metricScalar_smooth (I := I) (M := M) (S.family.metric t)).neg⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
@[simp] theorem conjCoeff_apply
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (t : Real) (x : M) :
    (conjCoeff (I := I) (M := M) S t : M → Real) x = -S.scalar t x := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_apply

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem conjCoeff_joint
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) :
    ContMDiffOn ((modelWithCornersSelf Real Real).prod I)
      (modelWithCornersSelf Real Real) ∞
      (fun p : Real × M =>
        (conjCoeff (I := I) (M := M) S p.1 : M → Real) p.2)
      (D.regular ×ˢ (Set.univ : Set M)) := by
  simpa only [conjCoeff_apply] using
    (scalar_joint (I := I) S hS).neg

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_joint then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_joint"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_joint ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_joint

noncomputable def conjCoeffRev
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (T : Real) :
    M × Real → Real := fun p =>
  (conjCoeff (I := I) (M := M) S (T - p.2) : M → Real) p.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeffRev then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeffRev"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeffRev ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeffRev

omit [NeZero (Module.finrank Real E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem conjCoeff_rev
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) :
    ContMDiffOn (I.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞
      (conjCoeffRev (I := I) (M := M) S (T : Real))
      ((Set.univ : Set M) ×ˢ {s : Real | (T : Real) - s ∈ D.regular}) := by
  have hmove :
      ContMDiffOn (I.prod (modelWithCornersSelf Real Real))
        ((modelWithCornersSelf Real Real).prod I) ∞
        (fun p : M × Real => ((T : Real) - p.2, p.1))
        ((Set.univ : Set M) ×ˢ {s : Real | (T : Real) - s ∈ D.regular}) := by
    exact ContMDiffOn.prodMk
      (ContMDiffOn.sub contMDiffOn_const contMDiffOn_snd)
      contMDiffOn_fst
  have hfun : conjCoeffRev (I := I) (M := M) S (T : Real) =
      (fun p : Real × M => (conjCoeff (I := I) (M := M) S p.1 : M → Real) p.2) ∘
        (fun p : M × Real => ((T : Real) - p.2, p.1)) := by
    funext p
    rfl
  rw [hfun]
  exact (conjCoeff_joint (I := I) S hS).comp hmove
    (fun p hp => ⟨hp.2, Set.mem_univ p.1⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_rev then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_rev"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_rev ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_rev

noncomputable def conjA1
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (T : D.RegularTime) (s : Real) :
    TensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 1 →L[Real]
      TensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 0 :=
  scalarPotH0 (I := I) (M := M) (S.family.metric (T : Real))
    (conjCoeff (I := I) (M := M) S ((T : Real) - s))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1 ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1

omit [BoundarylessManifold I M] in
theorem conjA1_cont
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) {A : Set Real}
    (hreg : ∀ s ∈ A, (T : Real) - s ∈ D.regular) :
    ContinuousOn (fun s : Real => conjA1 (I := I) (M := M) S T s) A := by
  let : SeminormedAddCommGroup
      (TensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 1 →L[Real]
        TensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 0) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  intro s0 hs0
  let K : D.RegularTime := ⟨(T : Real) - s0, hreg s0 hs0⟩
  have hshift :
      _root_.Filter.Tendsto (fun s : Real => (T : Real) - s)
        (𝓝 s0) (𝓝 (K : Real)) := by
    dsimp only [K]
    simpa only [id_eq] using
      (tendsto_const_nhds.sub
        (_root_.Filter.tendsto_id : _root_.Filter.Tendsto (fun s : Real => s) (𝓝 s0) (𝓝 s0)))
  change _root_.Filter.Tendsto
    (fun s : Real => conjA1 (I := I) (M := M) S T s)
    (𝓝[A] s0) (𝓝 (conjA1 (I := I) (M := M) S T s0))
  rw [Metric.tendsto_nhds]
  intro eta heta
  have heta2 : 0 < eta / 2 := half_pos heta
  have hcoef0 :
      ∀ᶠ t in 𝓝 (K : Real), ∀ x : M,
        |S.scalar t x - S.scalar (K : Real) x| < eta / 2 :=
    scalar_uniform (I := I) S hS K heta2
  have hcoef :
      ∀ᶠ s in 𝓝 s0, ∀ x : M,
        |S.scalar ((T : Real) - s) x -
          S.scalar ((T : Real) - s0) x| < eta / 2 := by
    exact hshift.eventually hcoef0
  filter_upwards [hcoef.filter_mono inf_le_left] with s hs
  rw [dist_eq_norm]
  have hpair := scalarPotH0_pair (I := I) (M := M)
    (S.family.metric (T : Real))
    (conjCoeff (I := I) (M := M) S ((T : Real) - s))
    (conjCoeff (I := I) (M := M) S ((T : Real) - s0)) heta2.le
    (fun x => by
      change |-S.scalar ((T : Real) - s) x -
        -S.scalar ((T : Real) - s0) x| ≤ eta / 2
      rw [neg_sub_neg, abs_sub_comm]
      exact (hs x).le)
  have hop :
      ‖conjA1 (I := I) (M := M) S T s -
          conjA1 (I := I) (M := M) S T s0‖ ≤ eta / 2 := by
    simpa only [conjA1] using hpair
  exact hop.trans_lt (half_lt_self heta)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1_cont ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1_cont

omit [BoundarylessManifold I M] in
theorem conjA1_short
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) :
    ∃ tau : Real, 0 < tau ∧ tau ≤ 1 ∧
      ∃ C1 : NNReal,
        ContinuousOn (fun s : Real => conjA1 (I := I) (M := M) S T s)
          (Set.Icc 0 tau) ∧
        _root_.MeasureTheory.AEStronglyMeasurable
          (fun s : Real => conjA1 (I := I) (M := M) S T s)
          (timeMeasure tau) ∧
        (∀ s ∈ Set.Icc 0 tau,
          ‖conjA1 (I := I) (M := M) S T s‖ ≤ (C1 : Real)) ∧
        ∀ᵐ s ∂timeMeasure tau,
          ‖conjA1 (I := I) (M := M) S T s‖ ≤ (C1 : Real) := by
  let : SeminormedAddCommGroup
      (TensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 1 →L[Real]
        TensorHs (I := I) (M := M) (S.family.metric (T : Real)) 0 0 0) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  have hshift :
      _root_.Filter.Tendsto (fun s : Real => (T : Real) - s)
        (𝓝 0) (𝓝 (T : Real)) := by
    simpa only [id_eq, sub_zero] using
      (tendsto_const_nhds.sub
        (_root_.Filter.tendsto_id : _root_.Filter.Tendsto (fun s : Real => s) (𝓝 0) (𝓝 0)))
  have hreg :
      ∀ᶠ s in 𝓝 (0 : Real), (T : Real) - s ∈ D.regular :=
    hshift.eventually (D.regular_isOpen.mem_nhds T.2)
  have hcoef :
      ∀ᶠ s in 𝓝 (0 : Real), ∀ x : M,
        |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| < 1 :=
    hshift.eventually (scalar_uniform (I := I) S hS T zero_lt_one)
  let U : Set Real := {s |
    (T : Real) - s ∈ D.regular ∧
      ∀ x : M,
        |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| ≤ 1}
  have hU : U ∈ 𝓝 (0 : Real) := by
    change ∀ᶠ s in 𝓝 (0 : Real),
      (T : Real) - s ∈ D.regular ∧
        ∀ x : M,
          |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| ≤ 1
    filter_upwards [hreg, hcoef] with s hs hc
    exact ⟨hs, fun x => (hc x).le⟩
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hU
  let tau : Real := _root_.Min.min 1 (delta / 2)
  have htaupos : 0 < tau := by
    dsimp only [tau]
    exact lt_min zero_lt_one (half_pos hdelta)
  have htauone : tau ≤ 1 := min_le_left _ _
  have htaudelta : tau < delta :=
    (min_le_right (1 : Real) (delta / 2)).trans_lt (half_lt_self hdelta)
  have hIccU : Set.Icc (0 : Real) tau ⊆ U := by
    intro s hs
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    exact hs.2.trans_lt htaudelta
  have hgood (s : Real) (hs : s ∈ Set.Icc (0 : Real) tau) :
      (T : Real) - s ∈ D.regular ∧
        ∀ x : M,
          |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| ≤ 1 := by
    simpa only [U, Set.mem_ofPred_eq] using hIccU hs
  have hRcont : Continuous (fun x : M => |S.scalar (T : Real) x|) := by
    have hscalar := metricScalar_smooth (I := I) (M := M)
      (S.family.metric (T : Real))
    simpa only [SolutionOn.scalar, SolutionFamily.scalar, SolutionOn.family]
      using hscalar.continuous.abs
  have hcompact : IsCompact (Set.range (fun x : M => |S.scalar (T : Real) x|)) :=
    isCompact_range hRcont
  obtain ⟨C0, hC0⟩ := hcompact.bddAbove
  have hC0x (x : M) : |S.scalar (T : Real) x| ≤ C0 :=
    hC0 ⟨x, rfl⟩
  let B : Real := _root_.Max.max 0 C0 + 1
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity
  let C1 : NNReal := ⟨B, hB0⟩
  have hcoefBound (s : Real) (hs : s ∈ Set.Icc (0 : Real) tau) (x : M) :
      |(conjCoeff (I := I) (M := M) S ((T : Real) - s) : M → Real) x| ≤ B := by
    rw [conjCoeff_apply, abs_neg]
    calc
      |S.scalar ((T : Real) - s) x| =
          |(S.scalar ((T : Real) - s) x - S.scalar (T : Real) x) +
            S.scalar (T : Real) x| := by
        congr 1
        ring
      _ ≤ |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| +
          |S.scalar (T : Real) x| := abs_add_le _ _
      _ ≤ 1 + C0 := add_le_add ((hgood s hs).2 x) (hC0x x)
      _ = C0 + 1 := add_comm _ _
      _ ≤ _root_.Max.max 0 C0 + 1 := add_le_add (le_max_right 0 C0) le_rfl
      _ = B := rfl
  have hcont :
      ContinuousOn (fun s : Real => conjA1 (I := I) (M := M) S T s)
        (Set.Icc 0 tau) :=
    conjA1_cont (I := I) (M := M) S hS T
      (fun s hs => (hgood s hs).1)
  have hmeas :
      _root_.MeasureTheory.AEStronglyMeasurable
        (fun s : Real => conjA1 (I := I) (M := M) S T s)
        (timeMeasure tau) := by
    unfold timeMeasure
    exact hcont.aestronglyMeasurable measurableSet_Icc
  have hboundOn :
      ∀ s ∈ Set.Icc (0 : Real) tau,
        ‖conjA1 (I := I) (M := M) S T s‖ ≤ (C1 : Real) := by
    intro s hs
    rw [conjA1, scalarPotH0_norm]
    exact scalarPotOp_norm (I := I) (M := M)
      (S.family.metric (T : Real))
      (conjCoeff (I := I) (M := M) S ((T : Real) - s)) hB0
      (hcoefBound s hs)
  have hboundAE :
      ∀ᵐ s ∂timeMeasure tau,
        ‖conjA1 (I := I) (M := M) S T s‖ ≤ (C1 : Real) := by
    unfold timeMeasure
    exact (_root_.MeasureTheory.ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall hboundOn)
  exact ⟨tau, htaupos, htauone, C1, hcont, hmeas, hboundOn, hboundAE⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1_short then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1_short"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1_short ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conjA1_short

omit [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [BoundarylessManifold I M] in
omit [SigmaCompactSpace M] in
theorem conjCoeff_bound
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : D.RegularTime) :
    ∃ tau : Real, 0 < tau ∧ tau ≤ 1 ∧
      ∃ C : Real, 0 ≤ C ∧
        ∀ s ∈ Set.Icc (0 : Real) tau, ∀ x : M,
          |(conjCoeff (I := I) (M := M) S
            ((T : Real) - s) : M → Real) x| ≤ C := by
  have hshift :
      _root_.Filter.Tendsto (fun s : Real => (T : Real) - s)
        (𝓝 0) (𝓝 (T : Real)) := by
    simpa only [id_eq, sub_zero] using
      (tendsto_const_nhds.sub
        (_root_.Filter.tendsto_id : _root_.Filter.Tendsto (fun s : Real => s) (𝓝 0) (𝓝 0)))
  have hcoef :
      ∀ᶠ s in 𝓝 (0 : Real), ∀ x : M,
        |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| < 1 :=
    hshift.eventually (scalar_uniform (I := I) S hS T zero_lt_one)
  let U : Set Real := {s |
    ∀ x : M,
      |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| ≤ 1}
  have hU : U ∈ 𝓝 (0 : Real) := by
    change ∀ᶠ s in 𝓝 (0 : Real),
      ∀ x : M,
        |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| ≤ 1
    filter_upwards [hcoef] with s hs
    exact fun x => (hs x).le
  obtain ⟨delta, hdelta, hball⟩ := Metric.mem_nhds_iff.mp hU
  let tau : Real := _root_.Min.min 1 (delta / 2)
  have htau : 0 < tau := by
    dsimp only [tau]
    exact lt_min zero_lt_one (half_pos hdelta)
  have htau_one : tau ≤ 1 := min_le_left _ _
  have htau_delta : tau < delta :=
    (min_le_right (1 : Real) (delta / 2)).trans_lt
      (half_lt_self hdelta)
  have hgood (s : Real) (hs : s ∈ Set.Icc (0 : Real) tau) : s ∈ U := by
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    exact hs.2.trans_lt htau_delta
  have hRcont : Continuous (fun x : M => |S.scalar (T : Real) x|) := by
    have hscalar := metricScalar_smooth (I := I) (M := M)
      (S.family.metric (T : Real))
    simpa only [SolutionOn.scalar, SolutionFamily.scalar, SolutionOn.family]
      using hscalar.continuous.abs
  obtain ⟨C0, hC0⟩ := (isCompact_range hRcont).bddAbove
  have hC0x (x : M) : |S.scalar (T : Real) x| ≤ C0 :=
    hC0 ⟨x, rfl⟩
  let C : Real := _root_.Max.max 0 C0 + 1
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨tau, htau, htau_one, C, hC, ?_⟩
  intro s hs x
  rw [conjCoeff_apply, abs_neg]
  calc
    |S.scalar ((T : Real) - s) x| =
        |(S.scalar ((T : Real) - s) x - S.scalar (T : Real) x) +
          S.scalar (T : Real) x| := by
      congr 1
      ring
    _ ≤ |S.scalar ((T : Real) - s) x - S.scalar (T : Real) x| +
        |S.scalar (T : Real) x| := abs_add_le _ _
    _ ≤ 1 + C0 := add_le_add (hgood s hs x) (hC0x x)
    _ = C0 + 1 := add_comm _ _
    _ ≤ _root_.Max.max 0 C0 + 1 := add_le_add (le_max_right 0 C0) le_rfl
    _ = C := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_bound ``Submission.DifferentialGeometry.PDE.RicciFlow.Entropy.conjCoeff_bound

end DifferentialGeometry.PDE.RicciFlow.Entropy

end
