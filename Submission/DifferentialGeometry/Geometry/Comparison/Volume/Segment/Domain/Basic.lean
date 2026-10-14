import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open _root_.Set _root_.Function _root_.Filter _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.MeasureTheory
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry : MeasurableSpace E := borel E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasurableSpace_differentialGeometry target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry : BorelSpace E := ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelSpace_differentialGeometry target :: scope.openDecls } }
private local instance instMeasTangent (x : M) : MeasurableSpace (TangentSpace I x) :=
  borel _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasTangent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instMeasTangent target :: scope.openDecls } }
private local instance instBorelTangent (x : M) : BorelSpace (TangentSpace I x) :=
  ⟨rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelTangent
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.instBorelTangent target :: scope.openDecls } }

def gBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) :
    Set (TangentSpace I x) :=
  {v | Real.sqrt (g.inner x v v) < R}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.gBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.gBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.gBall ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.gBall

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def SegmentDom [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) : Set (TangentSpace I x) :=
  {v | Real.sqrt (g.inner x v v)
        = (_root_.Manifold.riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v)).toReal}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.SegmentDom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.SegmentDom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.SegmentDom ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.SegmentDom

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem mem_segmentDom [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {x : M} {v : TangentSpace I x} :
    v ∈ SegmentDom (I := I) g hEnorm x ↔
      Real.sqrt (g.inner x v v)
        = (_root_.Manifold.riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v)).toReal :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.mem_segmentDom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.mem_segmentDom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.mem_segmentDom ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.mem_segmentDom

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem segmentDom_zero [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) : (0 : TangentSpace I x) ∈ SegmentDom (I := I) g hEnorm x := by
  rw [mem_segmentDom, expMapIntrinsic_zero (I := I) g hEnorm x,
    show g.inner x (0 : TangentSpace I x) (0 : TangentSpace I x) = 0 by simp,
    Real.sqrt_zero, Manifold.riemannianEDist_self, ENNReal.toReal_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentDom_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentDom_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentDom_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentDom_zero

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem segmentDom_smul [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {x : M} {v : TangentSpace I x} (hv : v ∈ SegmentDom (I := I) g hEnorm x)
    {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s • v ∈ SegmentDom (I := I) g hEnorm x := by
  set L : ℝ := Real.sqrt (g.inner x v v) with hL
  have hLnn : 0 ≤ L := Real.sqrt_nonneg _
  have h1s : 0 ≤ 1 - s := by linarith
  have hg0 : intrinsicGeodesic (I := I) g hEnorm x v 0 = x :=
    intrinsicGeodesic_zero (I := I) g hEnorm x v
  have hg1 : intrinsicGeodesic (I := I) g hEnorm x v 1
      = expMapIntrinsic (I := I) g hEnorm x v := rfl
  have hgs : intrinsicGeodesic (I := I) g hEnorm x v s
      = expMapIntrinsic (I := I) g hEnorm x (s • v) := by
    rw [expMapIntrinsic_def, intrinsicGeodesic_smul]
  have hvmem : L = (_root_.Manifold.riemannianEDist I x
      (expMapIntrinsic (I := I) g hEnorm x v)).toReal := hv
  have hfin1 : _root_.Manifold.riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v) ≠ ⊤ :=
    riemannianEDist_ne_top (I := I) x _
  have hedist1 : _root_.Manifold.riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v)
      = ENNReal.ofReal L := by
    rw [hvmem, ENNReal.ofReal_toReal hfin1]
  have hup : _root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
      (intrinsicGeodesic (I := I) g hEnorm x v s) ≤ ENNReal.ofReal (L * s) := by
    have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm x v
      (s := 0) (t := s) hs0
    rw [← hL, sub_zero] at h
    exact h
  have hup2 : _root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v s)
      (intrinsicGeodesic (I := I) g hEnorm x v 1)
      ≤ ENNReal.ofReal (L * (1 - s)) := by
    have h := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm x v
      (s := s) (t := 1) hs1
    rw [← hL] at h
    exact h
  have hsplit : ENNReal.ofReal L
      = ENNReal.ofReal (L * s) + ENNReal.ofReal (L * (1 - s)) := by
    rw [← ENNReal.ofReal_add (mul_nonneg hLnn hs0) (mul_nonneg hLnn h1s)]
    congr 1; ring
  have hlow : ENNReal.ofReal (L * s)
      ≤ _root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
          (intrinsicGeodesic (I := I) g hEnorm x v s) := by
    have htri : _root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
        (intrinsicGeodesic (I := I) g hEnorm x v 1)
        ≤ _root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
            (intrinsicGeodesic (I := I) g hEnorm x v s)
          + _root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v s)
              (intrinsicGeodesic (I := I) g hEnorm x v 1) :=
      _root_.Manifold.riemannianEDist_triangle
    have hchain : ENNReal.ofReal (L * s) + ENNReal.ofReal (L * (1 - s))
        ≤ _root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
            (intrinsicGeodesic (I := I) g hEnorm x v s)
          + ENNReal.ofReal (L * (1 - s)) := by
      calc ENNReal.ofReal (L * s) + ENNReal.ofReal (L * (1 - s))
          = _root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
              (intrinsicGeodesic (I := I) g hEnorm x v 1) := by
            rw [← hsplit, hg1, hg0, hedist1]
        _ ≤ _root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
              (intrinsicGeodesic (I := I) g hEnorm x v s)
            + _root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v s)
                (intrinsicGeodesic (I := I) g hEnorm x v 1) := htri
        _ ≤ _root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
              (intrinsicGeodesic (I := I) g hEnorm x v s)
            + ENNReal.ofReal (L * (1 - s)) := add_le_add le_rfl hup2
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp hchain
  have heq : _root_.Manifold.riemannianEDist I (intrinsicGeodesic (I := I) g hEnorm x v 0)
      (intrinsicGeodesic (I := I) g hEnorm x v s) = ENNReal.ofReal (L * s) :=
    le_antisymm hup hlow
  rw [hg0] at heq
  rw [mem_segmentDom, sqrt_gInner_smul_self (I := I) g x hs0 v, ← hL, ← hgs, heq,
    ENNReal.toReal_ofReal (mul_nonneg hLnn hs0)]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentDom_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentDom_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentDom_smul ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.segmentDom_smul

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem ball_sub_image_segmentDom [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) (R : ℝ) :
    {y : M | _root_.Manifold.riemannianEDist I x y < ENNReal.ofReal R} ⊆
      expMapIntrinsic (I := I) g hEnorm x ''
        (SegmentDom (I := I) g hEnorm x ∩ gBall (I := I) g x R) := by
  intro y hy
  obtain ⟨v, hexp, hlen⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm x y
  refine ⟨v, ⟨?_, ?_⟩, hexp⟩
  · rw [mem_segmentDom, hexp]; exact hlen
  · change Real.sqrt (g.inner x v v) < R
    rw [hlen]
    exact ENNReal.toReal_lt_of_lt_ofReal hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ball_sub_image_segmentDom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ball_sub_image_segmentDom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ball_sub_image_segmentDom ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.ball_sub_image_segmentDom

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless]
  [T2Space M]
  [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
theorem isOpen_gBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) :
    IsOpen (gBall (I := I) g x R) :=
  isOpen_lt (Real.continuous_sqrt.comp (continuous_gInner_self (I := I) g x))
    continuous_const

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.isOpen_gBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.isOpen_gBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.isOpen_gBall ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.isOpen_gBall

omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless]
  [T2Space M]
  [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
theorem measurableSet_gBall (g : SmoothRiemannianMetric I M) (x : M) (R : ℝ) :
    MeasurableSet (gBall (I := I) g x R) :=
  (isOpen_gBall (I := I) g x R).measurableSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.measurableSet_gBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.measurableSet_gBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.measurableSet_gBall ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.measurableSet_gBall

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem isClosed_segmentDom [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) : IsClosed (SegmentDom (I := I) g hEnorm x) := by
  have hf₁ : Continuous fun v : TangentSpace I x => Real.sqrt (g.inner x v v) :=
    Real.continuous_sqrt.comp (continuous_gInner_self (I := I) g x)
  have hexp : Continuous fun v : TangentSpace I x =>
      expMapIntrinsic (I := I) g hEnorm x v :=
    expMapIntrinsic_continuous (I := I) g hEnorm x
  have hbase : Continuous fun v : TangentSpace I x =>
      riemannianEDist I (expMapIntrinsic (I := I) g hEnorm x v) x :=
    (continuous_riemannianEDist_to (I := I) x).comp hexp
  have hedist : Continuous fun v : TangentSpace I x =>
      riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v) :=
    hbase.congr fun v => Manifold.riemannianEDist_comm
  have hf₂ : Continuous fun v : TangentSpace I x =>
      (_root_.Manifold.riemannianEDist I x (expMapIntrinsic (I := I) g hEnorm x v)).toReal :=
    ENNReal.continuousOn_toReal.comp_continuous hedist
      (fun v => riemannianEDist_ne_top (I := I) x _)
  exact isClosed_eq hf₁ hf₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.isClosed_segmentDom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.isClosed_segmentDom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.isClosed_segmentDom ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.isClosed_segmentDom

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem measurableSet_segmentDom [ConnectedSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (x : M) : MeasurableSet (SegmentDom (I := I) g hEnorm x) :=
  (isClosed_segmentDom (I := I) g hEnorm x).measurableSet

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.measurableSet_segmentDom then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.VolumeComparison.measurableSet_segmentDom"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.VolumeComparison.measurableSet_segmentDom ``Submission.DifferentialGeometry.Geometry.Riemannian.VolumeComparison.measurableSet_segmentDom

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
