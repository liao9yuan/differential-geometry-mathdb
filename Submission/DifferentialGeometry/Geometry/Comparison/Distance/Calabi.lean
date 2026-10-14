import Submission.DifferentialGeometry.Geometry.Geodesic.Maximal.Interval
import Submission.DifferentialGeometry.Geometry.Comparison.Variation.NoConjugatePoints.MinimizingSegment
import Submission.DifferentialGeometry.Geometry.Comparison.Laplacian.Radial
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Bishop.Intrinsic
import Submission.DifferentialGeometry.Geometry.Comparison.Volume.Bishop.IntrinsicLocal
import Submission.DifferentialGeometry.Geometry.Exponential.DiagonalExponential.LocalInverse
import Submission.DifferentialGeometry.Geometry.Exponential.Inverse.Branch
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Velocity
import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Submission.DifferentialGeometry.Geometry.Metric.Comparison.DistanceScaling

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection
open _root_.Submission.DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Topology
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.HopfRinow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
structure CalabiTail
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (O x : M) (r : Real) where
  splitPoint : M
  endpointVector : TangentSpace I splitPoint
  initialLength : Real
  terminalLength : Real
  branch : ExponentialInverseBranch (I := I) g hEnorm splitPoint
  conjugateScale : Real
  initialLength_pos : 0 < initialLength
  initialLength_nonneg : 0 ≤ initialLength
  terminalLength_pos : 0 < terminalLength
  length_sum : initialLength + terminalLength = r
  half_le_terminalLength : r / 2 ≤ terminalLength
  initial_edist : _root_.Manifold.riemannianEDist I O splitPoint = ENNReal.ofReal initialLength
  endpointVector_norm : Real.sqrt (g.inner splitPoint endpointVector endpointVector) = terminalLength
  source_mem : (endpointVector : E) ∈ branch.hom.source
  map_eq : branch.hom (endpointVector : E) = x
  one_lt_conjugateScale : 1 < conjugateScale
  no_conjugate :
    ∀ t ∈ Set.Ioo (0 : Real) conjugateScale,
      ¬ IsConjVec (I := I) g hEnorm splitPoint
        ((t • endpointVector : TangentSpace I splitPoint) : E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CalabiTail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CalabiTail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CalabiTail ``Submission.DifferentialGeometry.CalabiTail

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem CalabiTail.exp_eq
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w))}
    {O x : M} {r : Real}
    (tail : CalabiTail (I := I) g hEnorm O x r) :
    expMapIntrinsic (I := I) g hEnorm tail.splitPoint tail.endpointVector = x :=
  (tail.branch.hom_eq tail.source_mem).trans tail.map_eq

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.DifferentialGeometry.CalabiTail
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CalabiTail.exp_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CalabiTail.exp_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CalabiTail.exp_eq ``Submission.DifferentialGeometry.CalabiTail.exp_eq

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem CalabiTail.target_mem
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w))}
    {O x : M} {r : Real}
    (tail : CalabiTail (I := I) g hEnorm O x r) :
    x ∈ tail.branch.dom := by
  have hmem : tail.branch.hom (tail.endpointVector : E) ∈ tail.branch.hom.target :=
    tail.branch.hom.map_source tail.source_mem
  rw [tail.map_eq] at hmem
  exact hmem

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CalabiTail.target_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CalabiTail.target_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CalabiTail.target_mem ``Submission.DifferentialGeometry.CalabiTail.target_mem

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem CalabiTail.right_edist
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {O x : M} {r : Real}
    (tail : CalabiTail (I := I) g hEnorm O x r)
    (hr : r = (_root_.Manifold.riemannianEDist I O x).toReal) :
    riemannianEDist I tail.splitPoint x = ENNReal.ofReal tail.terminalLength := by
  have hrpos : 0 < r := by linarith [tail.initialLength_pos, tail.terminalLength_pos, tail.length_sum]
  have hfin : _root_.Manifold.riemannianEDist I O x ≠ (⊤ : ENNReal) := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hr
    linarith
  have hrE : _root_.Manifold.riemannianEDist I O x = ENNReal.ofReal r := by
    rw [hr, ENNReal.ofReal_toReal hfin]
  have hupper := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm tail.splitPoint tail.endpointVector
    (s := (0 : Real)) (t := 1) zero_le_one
  rw [intrinsicGeodesic_zero, ← expMapIntrinsic_def, tail.exp_eq, tail.endpointVector_norm,
    sub_zero, mul_one] at hupper
  refine le_antisymm hupper ?_
  have htri : _root_.Manifold.riemannianEDist I O x ≤
      riemannianEDist I O tail.splitPoint + _root_.Manifold.riemannianEDist I tail.splitPoint x :=
    Manifold.riemannianEDist_triangle
  rw [hrE, tail.initial_edist] at htri
  have hsplitE : ENNReal.ofReal r = ENNReal.ofReal tail.initialLength + ENNReal.ofReal tail.terminalLength := by
    rw [← ENNReal.ofReal_add tail.initialLength_nonneg tail.terminalLength_pos.le, tail.length_sum]
  rw [hsplitE] at htri
  exact (ENNReal.add_le_add_iff_left ENNReal.ofReal_ne_top).mp htri

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CalabiTail.right_edist then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CalabiTail.right_edist"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CalabiTail.right_edist ``Submission.DifferentialGeometry.CalabiTail.right_edist

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem CalabiTail.inner_normalized_tangent
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {O x : M} {r : Real}
    (tail : CalabiTail (I := I) g hEnorm O x r) :
    g.inner tail.splitPoint (tail.terminalLength⁻¹ • tail.endpointVector) (tail.terminalLength⁻¹ • tail.endpointVector) = 1 := by
  have hu_sq : g.inner tail.splitPoint tail.endpointVector tail.endpointVector = tail.terminalLength ^ 2 := by
    have hsq := Real.sq_sqrt
      (gInner_self_nonneg (I := I) g tail.splitPoint tail.endpointVector)
    rw [tail.endpointVector_norm] at hsq
    exact hsq.symm
  rw [gInner_smul_self (I := I) g tail.splitPoint, hu_sq]
  field_simp [tail.terminalLength_pos.ne']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CalabiTail.inner_normalized_tangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CalabiTail.inner_normalized_tangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CalabiTail.inner_normalized_tangent ``Submission.DifferentialGeometry.CalabiTail.inner_normalized_tangent

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem CalabiTail.intrinsicGeodesic_normalized_tangent_ell
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {O x : M} {r : Real}
    (tail : CalabiTail (I := I) g hEnorm O x r) :
    intrinsicGeodesic (I := I) g hEnorm tail.splitPoint (tail.terminalLength⁻¹ • tail.endpointVector) tail.terminalLength = x := by
  rw [← intrinsicGeodesic_smul (I := I) g hEnorm tail.splitPoint
    (tail.terminalLength⁻¹ • tail.endpointVector) tail.terminalLength, smul_smul,
    mul_inv_cancel₀ tail.terminalLength_pos.ne', one_smul, ← expMapIntrinsic_def]
  exact tail.exp_eq

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CalabiTail.intrinsicGeodesic_normalized_tangent_ell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CalabiTail.intrinsicGeodesic_normalized_tangent_ell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CalabiTail.intrinsicGeodesic_normalized_tangent_ell ``Submission.DifferentialGeometry.CalabiTail.intrinsicGeodesic_normalized_tangent_ell

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem CalabiTail.arcLength_normalized_tangent_le
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {O x : M} {r : Real}
    (tail : CalabiTail (I := I) g hEnorm O x r)
    (hr : r = (_root_.Manifold.riemannianEDist I O x).toReal)
    {eta : Real → M}
    (heta : ContMDiffOn 𝓘(Real, Real) I 1 eta (Set.Icc 0 tail.terminalLength))
    (heta0 : eta 0 = tail.splitPoint) (hetaell : eta tail.terminalLength = x) :
    Geometry.Riemannian.Variation.arcLength (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm tail.splitPoint (tail.terminalLength⁻¹ • tail.endpointVector))
        0 tail.terminalLength ≤ Geometry.Riemannian.Variation.arcLength (I := I) g eta 0 tail.terminalLength := by
  have heta_nonneg : 0 ≤ Geometry.Riemannian.Variation.arcLength (I := I) g eta 0 tail.terminalLength := by
    unfold Geometry.Riemannian.Variation.arcLength
    exact intervalIntegral.integral_nonneg tail.terminalLength_pos.le
      (fun _ _ => Real.sqrt_nonneg _)
  have hed : _root_.Manifold.riemannianEDist I (eta 0) (eta tail.terminalLength) ≤
      ENNReal.ofReal (Geometry.Riemannian.Variation.arcLength (I := I) g eta 0 tail.terminalLength) :=
    Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength
      (I := I) g tail.terminalLength_pos.le heta
      (fun t _ => hEnorm (eta t) _)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
  rw [heta0, hetaell, tail.right_edist hr,
    ENNReal.toReal_ofReal tail.terminalLength_pos.le,
    ENNReal.toReal_ofReal heta_nonneg] at hreal
  rw [arcLength_radial (I := I) g hEnorm tail.splitPoint (tail.terminalLength⁻¹ • tail.endpointVector),
    tail.inner_normalized_tangent, Real.sqrt_one, sub_zero, mul_one]
  exact hreal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CalabiTail.arcLength_normalized_tangent_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CalabiTail.arcLength_normalized_tangent_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CalabiTail.arcLength_normalized_tangent_le ``Submission.DifferentialGeometry.CalabiTail.arcLength_normalized_tangent_le

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def CalabiTail.shrink
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w))}
    {O x : M} {r b' : Real}
    (tail : CalabiTail (I := I) g hEnorm O x r)
    (hone : 1 < b') (hle : b' ≤ tail.conjugateScale) :
    CalabiTail (I := I) g hEnorm O x r where
  splitPoint := tail.splitPoint
  endpointVector := tail.endpointVector
  initialLength := tail.initialLength
  terminalLength := tail.terminalLength
  branch := tail.branch
  conjugateScale := b'
  initialLength_pos := tail.initialLength_pos
  initialLength_nonneg := tail.initialLength_nonneg
  terminalLength_pos := tail.terminalLength_pos
  length_sum := tail.length_sum
  half_le_terminalLength := tail.half_le_terminalLength
  initial_edist := tail.initial_edist
  endpointVector_norm := tail.endpointVector_norm
  source_mem := tail.source_mem
  map_eq := tail.map_eq
  one_lt_conjugateScale := hone
  no_conjugate := by
    intro t ht
    exact tail.no_conjugate t ⟨ht.1, ht.2.trans_le hle⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CalabiTail.shrink then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CalabiTail.shrink"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CalabiTail.shrink ``Submission.DifferentialGeometry.CalabiTail.shrink

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem CalabiTail.mem_eball
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w))}
    {O x : M} {r R t : Real}
    (tail : CalabiTail (I := I) g hEnorm O x r)
    (hreach : tail.initialLength + tail.terminalLength * tail.conjugateScale < R)
    (ht : t ∈ Set.Icc (0 : Real) tail.conjugateScale) :
    intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector t ∈
      Metric.eball O (ENNReal.ofReal R) := by
  have hellt : 0 ≤ tail.terminalLength * t :=
    mul_nonneg tail.terminalLength_pos.le ht.1
  have hdist :=
    intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm tail.splitPoint tail.endpointVector
      (s := (0 : Real)) (t := t) ht.1
  have hseg :
      _root_.Manifold.riemannianEDist I tail.splitPoint
          (intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector t) ≤
        ENNReal.ofReal (tail.terminalLength * t) := by
    rw [intrinsicGeodesic_zero (I := I) g hEnorm tail.splitPoint tail.endpointVector] at hdist
    simpa only [tail.endpointVector_norm, sub_zero] using hdist
  have hreal : tail.initialLength + tail.terminalLength * t < R := by
    have hmul : tail.terminalLength * t ≤ tail.terminalLength * tail.conjugateScale :=
      mul_le_mul_of_nonneg_left ht.2 tail.terminalLength_pos.le
    linarith
  have hR : 0 < R := by
    have hbase : 0 ≤ tail.initialLength + tail.terminalLength * t :=
      add_nonneg tail.initialLength_nonneg hellt
    linarith
  rw [Metric.mem_eball',
    IsRiemannianManifold.out (I := I) O
      (intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector t)]
  calc
    _root_.Manifold.riemannianEDist I O
        (intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector t) ≤
        _root_.Manifold.riemannianEDist I O tail.splitPoint +
          _root_.Manifold.riemannianEDist I tail.splitPoint
            (intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector t) :=
      Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal tail.initialLength + ENNReal.ofReal (tail.terminalLength * t) :=
      add_le_add tail.initial_edist.le hseg
    _ = ENNReal.ofReal (tail.initialLength + tail.terminalLength * t) :=
      (ENNReal.ofReal_add tail.initialLength_nonneg hellt).symm
    _ < ENNReal.ofReal R :=
      (ENNReal.ofReal_lt_ofReal_iff hR).2 hreal

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CalabiTail.mem_eball then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CalabiTail.mem_eball"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CalabiTail.mem_eball ``Submission.DifferentialGeometry.CalabiTail.mem_eball

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_calabiTail_of_split
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {O x : M} {r : Real} (v : TangentSpace I O)
    (hexp : expMapIntrinsic (I := I) g hEnorm O v = x)
    (hlen : Real.sqrt (g.inner O v v) = r)
    (hr : 0 < r)
    (hr_def : r = (_root_.Manifold.riemannianEDist I O x).toReal)
    (s₀ : Real) (hs₀ : s₀ ∈ Set.Ioo (0 : Real) 1) (hs₀half : s₀ ≤ 1 / 2) :
    ∃ tail : CalabiTail (I := I) g hEnorm O x r,
      tail.initialLength = s₀ * r ∧ tail.terminalLength = (1 - s₀) * r := by
  classical
  let z : TangentBundle I M :=
    intrinsicVelocityLift (I := I) g hEnorm O v s₀
  let u : TangentSpace I z.proj := (1 - s₀) • z.snd
  let zE : E := tangentSpaceModelContinuousLinearEquiv (I := I) z.proj z.snd
  let uE : E := (1 - s₀) • zE
  have huE :
      uE = tangentSpaceModelContinuousLinearEquiv (I := I) z.proj u := by
    dsimp only [uE, zE, u]
    rw [map_smul]
  let left : Real := s₀ * r
  let ell : Real := (1 - s₀) * r
  have hs₀_closed : s₀ ∈ Set.Icc (0 : Real) 1 :=
    ⟨hs₀.1.le, hs₀.2.le⟩
  have hfin : _root_.Manifold.riemannianEDist I O x ≠ (⊤ : ENNReal) := by
    intro htop
    rw [htop, ENNReal.toReal_top] at hr_def
    linarith
  have hlen_dist :
      Real.sqrt (g.inner O v v) =
        (_root_.Manifold.riemannianEDist I O x).toReal :=
    hlen.trans hr_def
  have hnot :
      ¬ IsConjVec (I := I) g hEnorm z.proj
        (tangentSpaceModelContinuousLinearEquiv (I := I) z.proj u) := by
    with_unfolding_all
      exact Geometry.Riemannian.Variation.tail_not_conj_of_min
        (I := I) g hEnorm v hexp hlen_dist (hr_def ▸ hr) hs₀
  obtain ⟨B, hsource⟩ :=
    branch_of_not_conj (I := I) g hEnorm hnot
  have hexp_tail :
      expMapIntrinsic (I := I) g hEnorm z.proj u = x := by
    have hcontinue :=
      congrFun
        (intrinsicGeodesic_continuation
          (I := I) g hEnorm O v s₀) (1 - s₀)
    have hend :
        intrinsicGeodesic (I := I) g hEnorm O v 1 = x := by
      simpa only [expMapIntrinsic_def] using hexp
    change intrinsicGeodesic (I := I) g hEnorm z.proj u 1 = x
    dsimp only [u]
    rw [intrinsicGeodesic_smul (I := I) g hEnorm]
    rw [show z.proj =
        intrinsicGeodesic (I := I) g hEnorm O v s₀ by
          exact Geometry.Riemannian.Exponential.velocityLift_proj
            (I := I) g hEnorm O v s₀]
    rw [show z.snd =
        (mfderiv 𝓘(Real, Real) I
          (intrinsicGeodesic (I := I) g hEnorm O v) s₀ :
            Real →L[Real] TangentSpace I
              (intrinsicGeodesic (I := I) g hEnorm O v s₀)) 1 by rfl]
    calc
      intrinsicGeodesic (I := I) g hEnorm
          (intrinsicGeodesic (I := I) g hEnorm O v s₀)
          (mfderiv 𝓘(Real, Real) I
            (intrinsicGeodesic (I := I) g hEnorm O v) s₀ 1)
          (1 - s₀) =
          intrinsicGeodesic (I := I) g hEnorm O v (1 - s₀ + s₀) :=
        hcontinue.symm
      _ = intrinsicGeodesic (I := I) g hEnorm O v 1 := by
        congr 1
        ring
      _ = x := hend
  have hmap_eq : B.hom uE = x :=
    by
      rw [huE]
      exact (B.hom_eq hsource).symm.trans hexp_tail
  have hscale_cont : Continuous (fun t : Real => t • uE) :=
    continuous_id.smul continuous_const
  have hsource_nhds :
      {t : Real | t • uE ∈ B.hom.source} ∈ 𝓝 (1 : Real) := by
    apply hscale_cont.continuousAt.preimage_mem_nhds
    rw [huE]
    simpa only [one_smul] using B.hom.open_source.mem_nhds hsource
  obtain ⟨ε, hε, hε_sub⟩ := Metric.mem_nhds_iff.mp hsource_nhds
  let b : Real := 1 + ε / 2
  have hb : 1 < b := by
    dsimp [b]
    linarith
  have hsource_tail :
      ∀ t ∈ Set.Icc (1 : Real) b,
        t • uE ∈ B.hom.source := by
    intro t ht
    apply hε_sub
    rw [Metric.mem_ball, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr ht.1)]
    dsimp [b] at ht
    calc
      t - 1 ≤ ε / 2 := by linarith [ht.2]
      _ < ε := by linarith [hε]
  have htail_no :
      ∀ t ∈ Set.Ioc (0 : Real) 1,
        ¬ IsConjVec (I := I) g hEnorm z.proj
          (t • uE) := by
    intro t ht
    have htModel :
        t • uE = tangentSpaceModelContinuousLinearEquiv (I := I) z.proj (t • u) := by
      dsimp only [uE, zE, u]
      rw [map_smul, map_smul]
    rw [htModel]
    with_unfolding_all
      exact Geometry.Riemannian.Variation.tail_no_conj
        (I := I) g hEnorm v hexp hlen_dist (hr_def ▸ hr) hs₀ t ht
  have hno :
      ∀ t ∈ Set.Ioo (0 : Real) b,
        ¬ IsConjVec (I := I) g hEnorm z.proj
          (t • uE) := by
    intro t ht
    rcases le_total t 1 with ht1 | h1t
    · exact htail_no t ⟨ht.1, ht1⟩
    · exact B.not_conj (hsource_tail t ⟨h1t, ht.2.le⟩)
  have hspeed :
      g.inner z.proj z.snd z.snd = g.inner O v v := by
    rw [show z.proj = intrinsicGeodesic (I := I) g hEnorm O v s₀ by
      exact Geometry.Riemannian.Exponential.velocityLift_proj
        (I := I) g hEnorm O v s₀]
    rw [show z.snd =
        (mfderiv 𝓘(Real, Real) I
          (intrinsicGeodesic (I := I) g hEnorm O v) s₀ :
            Real →L[Real] TangentSpace I
              (intrinsicGeodesic (I := I) g hEnorm O v s₀)) 1 by rfl]
    exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm O v s₀
  have hu_norm :
      Real.sqrt (g.inner z.proj u u) = ell := by
    dsimp only [u]
    rw [sqrt_gInner_smul_self (I := I) g z.proj
      (sub_nonneg.mpr hs₀.2.le) z.snd, hspeed, hlen]
  have hleft :
      riemannianEDist I O z.proj = ENNReal.ofReal left := by
    simpa only [z, Geometry.Riemannian.Exponential.velocityLift_proj, left] using
      Geometry.Riemannian.Variation.minSegment_edist
        (I := I) g hEnorm v hexp hlen hr_def hfin hs₀_closed
  have hleftPos : 0 < left := by
    exact mul_pos hs₀.1 hr
  refine ⟨{
    splitPoint := z.proj
    endpointVector := u
    initialLength := left
    terminalLength := ell
    branch := B
    conjugateScale := b
    initialLength_pos := hleftPos
    initialLength_nonneg := hleftPos.le
    terminalLength_pos := by
      exact mul_pos (sub_pos.mpr hs₀.2) hr
    length_sum := by
      dsimp [left, ell]
      ring
    half_le_terminalLength := by
      dsimp only [ell]
      nlinarith
    initial_edist := hleft
    endpointVector_norm := hu_norm
    source_mem := hsource
    map_eq := hmap_eq
    one_lt_conjugateScale := hb
    no_conjugate := hno
  }, rfl, rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_calabiTail_of_split then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_calabiTail_of_split"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_calabiTail_of_split ``Submission.DifferentialGeometry.exists_calabiTail_of_split

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_calabiTail
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {O x : M} {r : Real} (v : TangentSpace I O)
    (hexp : expMapIntrinsic (I := I) g hEnorm O v = x)
    (hlen : Real.sqrt (g.inner O v v) = r)
    (hr : 0 < r)
    (hr_def : r = (_root_.Manifold.riemannianEDist I O x).toReal) :
    Nonempty (CalabiTail (I := I) g hEnorm O x r) := by
  obtain ⟨tail, -, -⟩ := exists_calabiTail_of_split
    (I := I) g hEnorm v hexp hlen hr hr_def (1 / 4) (by norm_num) (by norm_num)
  exact ⟨tail⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_calabiTail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_calabiTail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_calabiTail ``Submission.DifferentialGeometry.exists_calabiTail

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_calabiTail_lt
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {O x : M} {r R : Real} (v : TangentSpace I O)
    (hexp : expMapIntrinsic (I := I) g hEnorm O v = x)
    (hlen : Real.sqrt (g.inner O v v) = r)
    (hr : 0 < r)
    (hr_def : r = (_root_.Manifold.riemannianEDist I O x).toReal)
    (hrR : r < R) :
    ∃ tail : CalabiTail (I := I) g hEnorm O x r,
      tail.initialLength + tail.terminalLength * tail.conjugateScale < R := by
  obtain ⟨tail⟩ :=
    exists_calabiTail (I := I) g hEnorm v hexp hlen hr hr_def
  let b' : Real :=
    _root_.Min.min tail.conjugateScale (1 + (R - r) / (2 * tail.terminalLength))
  have hgap : 0 < R - r := sub_pos.mpr hrR
  have hden : 0 < 2 * tail.terminalLength := mul_pos (by norm_num) tail.terminalLength_pos
  have haux : 1 < 1 + (R - r) / (2 * tail.terminalLength) := by
    have : 0 < (R - r) / (2 * tail.terminalLength) := div_pos hgap hden
    linarith
  have hb' : 1 < b' := by
    exact lt_min tail.one_lt_conjugateScale haux
  have hb_le : b' ≤ tail.conjugateScale := min_le_left _ _
  let tail' : CalabiTail (I := I) g hEnorm O x r :=
    tail.shrink hb' hb_le
  refine ⟨tail', ?_⟩
  change tail.initialLength + tail.terminalLength * b' < R
  have hb_aux : b' ≤ 1 + (R - r) / (2 * tail.terminalLength) :=
    min_le_right _ _
  have hmul :
      tail.terminalLength * b' ≤
        tail.terminalLength * (1 + (R - r) / (2 * tail.terminalLength)) :=
    mul_le_mul_of_nonneg_left hb_aux tail.terminalLength_pos.le
  have hscale :
      tail.terminalLength * (1 + (R - r) / (2 * tail.terminalLength)) =
        tail.terminalLength + (R - r) / 2 := by
    field_simp [ne_of_gt tail.terminalLength_pos]
  calc
    tail.initialLength + tail.terminalLength * b' ≤
        tail.initialLength +
          tail.terminalLength * (1 + (R - r) / (2 * tail.terminalLength)) :=
      by linarith
    _ = r + (R - r) / 2 := by
      rw [hscale]
      linarith [tail.length_sum]
    _ < R := by linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_calabiTail_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_calabiTail_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_calabiTail_lt ``Submission.DifferentialGeometry.exists_calabiTail_lt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem calabi_support_of_tail_of_frame
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    {O x : M} {r : Real}
    (tail : CalabiTail (I := I) g hEnorm O x r)
    (w : Fin (Module.finrank Real E - 1) → TangentSpace I tail.splitPoint)
    (hwLI : LinearIndependent Real w)
    (hwperp : ∀ i, g.inner tail.splitPoint tail.endpointVector (w i) = 0) :
    let rho : M → Real := fun y =>
      tail.initialLength + Geometry.Riemannian.Exponential.branchRadius
        (I := I) g tail.branch y
    ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
    rho x = r ∧
    (∀ᶠ y in 𝓝 x, (_root_.Manifold.riemannianEDist I O y).toReal ≤ rho y) ∧
    (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) rho y) ∧
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M => gradientFun (I := I) g rho y) x ∧
    g.inner x
        (gradientFun (I := I) g rho x)
        (gradientFun (I := I) g rho x) = 1 ∧
    laplacian (I := I) (LeviCivita (I := I) g) g rho x =
      Geometry.Riemannian.Variation.curveMean (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector)
          (fun i => intrinsicJacobi (I := I) g hEnorm tail.splitPoint tail.endpointVector (w i)) 1 /
        tail.terminalLength := by
  classical
  dsimp only
  have hsqrt_pos :
      0 < Real.sqrt (g.inner tail.splitPoint tail.endpointVector tail.endpointVector) := by
    rw [tail.endpointVector_norm]
    exact tail.terminalLength_pos
  have hu_pos : 0 < g.inner tail.splitPoint tail.endpointVector tail.endpointVector :=
    Real.sqrt_pos.mp hsqrt_pos
  let rho : M → Real := fun y =>
    tail.initialLength + branchRadius (I := I) g tail.branch y
  have hbr_inf :
      ContMDiffAt I 𝓘(Real, Real) ∞
        (branchRadius (I := I) g tail.branch) x := by
    have h :=
      branchRadius_infAt (I := I) tail.branch tail.source_mem hu_pos
    rw [tail.exp_eq] at h
    exact h
  have hrho_inf : ContMDiffAt I 𝓘(Real, Real) ∞ rho x := by
    exact contMDiffAt_const.add hbr_inf
  have hrad_x :
      branchRadius (I := I) g tail.branch x = tail.terminalLength := by
    calc
      branchRadius (I := I) g tail.branch x =
          branchRadius (I := I) g tail.branch
            (expMapIntrinsic (I := I) g hEnorm tail.splitPoint tail.endpointVector) :=
        congrArg (branchRadius (I := I) g tail.branch) tail.exp_eq.symm
      _ = Real.sqrt (g.inner tail.splitPoint tail.endpointVector tail.endpointVector) :=
        branchRadius_exp (I := I) tail.branch tail.source_mem
      _ = tail.terminalLength := tail.endpointVector_norm
  have hrho_x : rho x = r := by
    dsimp only [rho]
    rw [hrad_x, tail.length_sum]
  have hupper :
      ∀ᶠ y in 𝓝 x,
        (_root_.Manifold.riemannianEDist I O y).toReal ≤ rho y := by
    filter_upwards [
      tail.branch.hom.open_target.mem_nhds tail.target_mem] with y hy
    have hrad_nonneg :
        0 ≤ branchRadius (I := I) g tail.branch y :=
      Real.sqrt_nonneg _
    have hdist :
        _root_.Manifold.riemannianEDist I O y ≤
          ENNReal.ofReal tail.initialLength +
            ENNReal.ofReal
              (branchRadius (I := I) g tail.branch y) := by
      calc
        _root_.Manifold.riemannianEDist I O y ≤
            _root_.Manifold.riemannianEDist I O tail.splitPoint +
              riemannianEDist I tail.splitPoint y :=
          Manifold.riemannianEDist_triangle
        _ ≤ ENNReal.ofReal tail.initialLength +
              ENNReal.ofReal
                (branchRadius (I := I) g tail.branch y) := by
          exact add_le_add tail.initial_edist.le
            (tail.branch.edist_le_radius hy)
    have hreal :=
      ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr
          ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hdist
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal tail.initialLength_nonneg,
      ENNReal.toReal_ofReal hrad_nonneg] at hreal
    exact hreal
  have hbr_diff :
      MDifferentiableAt I 𝓘(Real, Real)
        (branchRadius (I := I) g tail.branch) x :=
    hbr_inf.mdifferentiableAt (by simp)
  have hgrad_rho :
      gradientFun (I := I) g rho x =
        gradientFun (I := I) g
          (branchRadius (I := I) g tail.branch) x := by
    calc
      gradientFun (I := I) g rho x =
          gradientFun (I := I) g (fun _ : M => tail.initialLength) x +
            gradientFun (I := I) g
              (branchRadius (I := I) g tail.branch) x := by
        exact gradientFun_add (I := I) g
          mdifferentiableAt_const hbr_diff
      _ = gradientFun (I := I) g
            (branchRadius (I := I) g tail.branch) x := by
        rw [gradientFun_const, zero_add]
  let velocityAtOne : TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector 1) :=
    (mfderiv 𝓘(Real, Real) I
      (intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector) 1) 1
  let velocityE : E :=
    tangentSpaceModelContinuousLinearEquiv (I := I)
      (intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector 1) velocityAtOne
  let Vx : TangentSpace I x :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
      velocityE
  have hgrad_br :
      gradientFun (I := I) g
          (branchRadius (I := I) g tail.branch) x =
        (Real.sqrt (g.inner tail.splitPoint tail.endpointVector tail.endpointVector))⁻¹ •
          Vx := by
    have h :=
      grad_branchRadius
        (I := I) tail.branch tail.source_mem hu_pos
    rw [tail.exp_eq] at h
    dsimp only [Vx, velocityE, velocityAtOne]
    with_unfolding_all
      convert h using 1
      all_goals rfl
  have hspeed :
      g.inner x Vx Vx =
        g.inner tail.splitPoint tail.endpointVector tail.endpointVector := by
    have h :=
      intrinsicGeodesic_speedSq_eq
        (I := I) g hEnorm tail.splitPoint tail.endpointVector 1
    rw [← expMapIntrinsic_def, tail.exp_eq] at h
    dsimp only [Vx, velocityE, velocityAtOne]
    convert h using 1
    all_goals rfl
  have hu_sq :
      g.inner tail.splitPoint tail.endpointVector tail.endpointVector = tail.terminalLength ^ 2 := by
    have hsq :=
      Real.sq_sqrt
        (gInner_self_nonneg (I := I) g tail.splitPoint tail.endpointVector)
    rw [tail.endpointVector_norm] at hsq
    exact hsq.symm
  have hgrad_norm :
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) = 1 := by
    rw [hgrad_rho, hgrad_br,
      gInner_smul_self (I := I) g x, hspeed, tail.endpointVector_norm,
      hu_sq]
    field_simp [tail.terminalLength_pos.ne']
  obtain ⟨U, hUopen, hxU, hbrU⟩ :=
    branchRadius_open
      (I := I) tail.branch tail.source_mem hu_pos
  rw [tail.exp_eq] at hxU
  have hrhoU :
      ContMDiffOn I 𝓘(Real, Real) ∞ rho U := by
    dsimp only [rho]
    change ContMDiffOn I 𝓘(Real, Real) ∞
      ((fun _ : M => tail.initialLength) + branchRadius (I := I) g tail.branch) U
    exact contMDiffOn_const.add hbrU
  have hrho_ev :
      ∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) rho y := by
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact
      ((hrhoU y hy).contMDiffAt
        (hUopen.mem_nhds hy)).mdifferentiableAt (by simp)
  have hrho_grad :
      MDiffAt
        (T% fun y : M =>
          gradientFun (I := I) g rho y) x :=
    gradientFun_mdiffOn (I := I) g hUopen hrhoU hxU
  have hbr_ev :
      ∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real)
          (branchRadius (I := I) g tail.branch) y := by
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    exact
      ((hbrU y hy).contMDiffAt
        (hUopen.mem_nhds hy)).mdifferentiableAt (by simp)
  have hbr_grad :
      MDiffAt
        (T% fun y : M =>
          gradientFun (I := I) g
            (branchRadius (I := I) g tail.branch) y) x :=
    gradientFun_mdiffOn (I := I) g hUopen hbrU hxU
  have hlap_rho :
      laplacian (I := I) (LeviCivita (I := I) g) g rho x =
        laplacian (I := I) (LeviCivita (I := I) g) g
          (branchRadius (I := I) g tail.branch) x := by
    exact laplacian_add_const
      (I := I) (LeviCivita (I := I) g) g tail.initialLength hbr_ev hbr_grad
  have hlap_br :=
    branchLap_eq_mean
      (I := I) g hEnorm tail.branch tail.endpointVector w
        tail.source_mem hu_pos hwLI hwperp (by simp)
  dsimp only at hlap_br
  rw [← expMapIntrinsic_def, tail.exp_eq, tail.endpointVector_norm] at hlap_br
  refine ⟨hrho_inf, hrho_x, hupper, hrho_ev, hrho_grad,
    hgrad_norm, hlap_rho.trans hlap_br⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.calabi_support_of_tail_of_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.calabi_support_of_tail_of_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.calabi_support_of_tail_of_frame ``Submission.DifferentialGeometry.calabi_support_of_tail_of_frame

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem CalabiTail.inner_grad_support_eq_deriv
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    {g : SmoothRiemannianMetric I M}
    {hEnorm : IsMetricNorm (I := I) (M := M) g}
    {O x : M} {r : Real}
    (tail : CalabiTail (I := I) g hEnorm O x r)
    (F : C^∞⟮I, M; Real⟯) :
    g.inner x (gradFun (I := I) g F x)
        (gradientFun (I := I) g
          (fun y => tail.initialLength + branchRadius (I := I) g tail.branch y) x) =
      deriv (F ∘ intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector) 1 /
        tail.terminalLength := by
  have hu_pos : 0 < g.inner tail.splitPoint tail.endpointVector tail.endpointVector := by
    apply Real.sqrt_pos.mp
    rw [tail.endpointVector_norm]
    exact tail.terminalLength_pos
  let rho : M → Real := fun y =>
    tail.initialLength + branchRadius (I := I) g tail.branch y
  have hbr_inf :
      ContMDiffAt I 𝓘(Real, Real) ∞
        (branchRadius (I := I) g tail.branch) x := by
    have h :=
      branchRadius_infAt (I := I) tail.branch tail.source_mem hu_pos
    rw [tail.exp_eq] at h
    exact h
  have hbr_diff :
      MDifferentiableAt I 𝓘(Real, Real)
        (branchRadius (I := I) g tail.branch) x :=
    hbr_inf.mdifferentiableAt (by simp)
  have hgrad_rho :
      gradientFun (I := I) g rho x =
        gradientFun (I := I) g
          (branchRadius (I := I) g tail.branch) x := by
    calc
      gradientFun (I := I) g rho x =
          gradientFun (I := I) g (fun _ : M => tail.initialLength) x +
            gradientFun (I := I) g
              (branchRadius (I := I) g tail.branch) x := by
        exact gradientFun_add (I := I) g
          mdifferentiableAt_const hbr_diff
      _ = gradientFun (I := I) g
            (branchRadius (I := I) g tail.branch) x := by
        rw [gradientFun_const, zero_add]
  let velocityAtOne : TangentSpace I
      (intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector 1) :=
    (mfderiv 𝓘(Real, Real) I
      (intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector) 1) 1
  let velocityE : E :=
    tangentSpaceModelContinuousLinearEquiv (I := I)
      (intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector 1) velocityAtOne
  let Vx : TangentSpace I x :=
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm velocityE
  have hgrad_br :
      gradientFun (I := I) g
          (branchRadius (I := I) g tail.branch) x =
        (Real.sqrt (g.inner tail.splitPoint tail.endpointVector tail.endpointVector))⁻¹ • Vx := by
    have h :=
      grad_branchRadius (I := I) tail.branch tail.source_mem hu_pos
    rw [tail.exp_eq] at h
    dsimp only [Vx, velocityE, velocityAtOne]
    with_unfolding_all
      convert h using 1
      all_goals rfl
  have hderiv :
      deriv (F ∘ intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector) 1 =
        g.inner x (gradFun (I := I) g F x) Vx := by
    have h := deriv_comp_eq_inner_grad_velocity (I := I) g F.contMDiff
      (intrinsicGeodesic_contMDiff (I := I) g hEnorm tail.splitPoint tail.endpointVector) 1
    rw [← expMapIntrinsic_def, tail.exp_eq] at h
    dsimp only [Vx, velocityE, velocityAtOne]
    with_unfolding_all
      convert h using 1
      all_goals rfl
  change g.inner x (gradFun (I := I) g F x)
      (gradientFun (I := I) g rho x) = _
  rw [hgrad_rho, hgrad_br, map_smul, smul_eq_mul,
    tail.endpointVector_norm, hderiv]
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.CalabiTail.inner_grad_support_eq_deriv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.CalabiTail.inner_grad_support_eq_deriv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.CalabiTail.inner_grad_support_eq_deriv ``Submission.DifferentialGeometry.CalabiTail.inner_grad_support_eq_deriv

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem calabi_support_of_tail
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (q : Real) (hq : 0 ≤ q)
    {O x : M} {r : Real}
    (tail : CalabiTail (I := I) g hEnorm O x r)
    (hRic : 0 < Module.finrank Real E - 1 →
      let γ : Real → M :=
        intrinsicGeodesic (I := I) g hEnorm tail.splitPoint tail.endpointVector
      ∀ t ∈ Set.Ioo (0 : Real) tail.conjugateScale,
        -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) *
            g.inner (γ t)
              (Geometry.Riemannian.Variation.curveVelocity (I := I) γ t)
              (Geometry.Riemannian.Variation.curveVelocity (I := I) γ t) ≤
          ricciTensor (I := I) g (γ t)
            (Geometry.Riemannian.Variation.curveVelocity (I := I) γ t)
            (Geometry.Riemannian.Variation.curveVelocity (I := I) γ t)) :
    let rho : M → Real := fun y =>
      tail.initialLength + Geometry.Riemannian.Exponential.branchRadius
        (I := I) g tail.branch y
    ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
    rho x = r ∧
    (∀ᶠ y in 𝓝 x, (_root_.Manifold.riemannianEDist I O y).toReal ≤ rho y) ∧
    (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) rho y) ∧
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M => gradientFun (I := I) g rho y) x ∧
    g.inner x
        (gradientFun (I := I) g rho x)
        (gradientFun (I := I) g rho x) = 1 ∧
    laplacian (I := I) (LeviCivita (I := I) g) g rho x ≤
      2 * ((Module.finrank Real E - 1 : Nat) : Real) / r +
        ((Module.finrank Real E - 1 : Nat) : Real) * q := by
  classical
  dsimp only
  have hr : 0 < r := by
    rw [← tail.length_sum]
    exact add_pos tail.initialLength_pos tail.terminalLength_pos
  have hu_pos : 0 < g.inner tail.splitPoint tail.endpointVector tail.endpointVector := by
    apply Real.sqrt_pos.mp
    rw [tail.endpointVector_norm]
    exact tail.terminalLength_pos
  obtain ⟨w, hwLI, hwperp, hmean⟩ :=
    Geometry.Riemannian.VolumeComparison.exists_intrMean_on
      (I := I) g hEnorm tail.splitPoint tail.endpointVector q tail.conjugateScale
        hq tail.one_lt_conjugateScale hu_pos tail.no_conjugate hRic
  obtain ⟨hrho_inf, hrho_x, hupper, hrho_ev, hrho_grad,
      hgrad_norm, hlap_eq⟩ :=
    calabi_support_of_tail_of_frame
      (I := I) g hEnorm tail w hwLI hwperp
  dsimp only at hmean
  rw [tail.endpointVector_norm] at hmean
  have hlap_bound :
      laplacian (I := I) (LeviCivita (I := I) g) g
          (fun y => tail.initialLength + branchRadius (I := I) g tail.branch y) x ≤
        ((Module.finrank Real E - 1 : Nat) : Real) / tail.terminalLength +
          ((Module.finrank Real E - 1 : Nat) : Real) * q := by
    rw [hlap_eq]
    exact hmean
  have hfrac :
      ((Module.finrank Real E - 1 : Nat) : Real) / tail.terminalLength ≤
        2 * ((Module.finrank Real E - 1 : Nat) : Real) / r := by
    apply (div_le_iff₀ tail.terminalLength_pos).2
    rw [show
      2 * ((Module.finrank Real E - 1 : Nat) : Real) / r * tail.terminalLength =
        (2 * ((Module.finrank Real E - 1 : Nat) : Real) * tail.terminalLength) / r by
          ring]
    apply (le_div_iff₀ hr).2
    have hn :
        0 ≤ ((Module.finrank Real E - 1 : Nat) : Real) :=
      Nat.cast_nonneg _
    have hrell : r ≤ 2 * tail.terminalLength := by
      linarith [tail.half_le_terminalLength]
    nlinarith [mul_nonneg hn (sub_nonneg.mpr hrell)]
  refine ⟨hrho_inf, hrho_x, hupper, hrho_ev, hrho_grad,
    hgrad_norm, ?_⟩
  linarith

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.calabi_support_of_tail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.calabi_support_of_tail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.calabi_support_of_tail ``Submission.DifferentialGeometry.calabi_support_of_tail

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_calabiData_lt
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (q : Real) (hq : 0 ≤ q)
    {O x : M} {R : Real}
    (hRic : 0 < Module.finrank Real E - 1 →
      ∀ y ∈ Metric.eball O (ENNReal.ofReal R),
        ∀ w : TangentSpace I y,
          -(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2) *
              g.inner y w w ≤ ricciTensor (I := I) g y w w)
    (hOx : O ≠ x)
    (hfin : _root_.Manifold.riemannianEDist I O x ≠ (⊤ : ENNReal))
    (hR : (_root_.Manifold.riemannianEDist I O x).toReal < R) :
    let r := (_root_.Manifold.riemannianEDist I O x).toReal
    ∃ tail : CalabiTail (I := I) g hEnorm O x r,
      tail.initialLength + tail.terminalLength * tail.conjugateScale < R ∧
      let rho : M → Real := fun y =>
        tail.initialLength + branchRadius (I := I) g tail.branch y
      ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
      rho x = r ∧
      (∀ᶠ y in 𝓝 x, (_root_.Manifold.riemannianEDist I O y).toReal ≤ rho y) ∧
      (∀ᶠ y in 𝓝 x, MDifferentiableAt I 𝓘(Real, Real) rho y) ∧
      MDifferentiableAt I (I.prod 𝓘(Real, E))
        (T% fun y : M => gradientFun (I := I) g rho y) x ∧
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) = 1 ∧
      laplacian (I := I) (LeviCivita (I := I) g) g rho x ≤
        2 * ((Module.finrank Real E - 1 : Nat) : Real) / r +
          ((Module.finrank Real E - 1 : Nat) : Real) * q := by
  classical
  dsimp only
  let r : Real := (_root_.Manifold.riemannianEDist I O x).toReal
  have hdist_ne : _root_.Manifold.riemannianEDist I O x ≠ 0 := by
    intro hzero
    exact hOx (riemannianEDist_eq_zero_imp_eq (I := I) O x hzero)
  have hr : 0 < r :=
    ENNReal.toReal_pos hdist_ne hfin
  obtain ⟨v, hexp, hlen⟩ :=
    minExp_of_ne_top (I := I) g hEnorm O x hfin
  obtain ⟨tail, hreach⟩ :=
    exists_calabiTail_lt (I := I) g hEnorm v hexp hlen hr rfl hR
  refine ⟨tail, hreach,
    calabi_support_of_tail (I := I) g hEnorm q hq tail ?_⟩
  intro hd
  dsimp only
  intro t ht
  apply hRic hd _ (tail.mem_eball hreach ⟨ht.1.le, ht.2.le⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_calabiData_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_calabiData_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_calabiData_lt ``Submission.DifferentialGeometry.exists_calabiData_lt

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_calabiData
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (q : Real) (hq : 0 ≤ q)
    (hRic : Geometry.Riemannian.BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)))
    {O x : M} (hOx : O ≠ x)
    (hfin : _root_.Manifold.riemannianEDist I O x ≠ (⊤ : ENNReal)) :
    let r := (_root_.Manifold.riemannianEDist I O x).toReal
    ∃ tail : CalabiTail (I := I) g hEnorm O x r,
      let rho : M → Real := fun y =>
        tail.initialLength + branchRadius (I := I) g tail.branch y
      ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
      rho x = r ∧
      (∀ᶠ y in 𝓝 x,
        (_root_.Manifold.riemannianEDist I O y).toReal ≤ rho y) ∧
      (∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) rho y) ∧
      MDifferentiableAt I (I.prod 𝓘(Real, E))
        (T% fun y : M => gradientFun (I := I) g rho y) x ∧
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) = 1 ∧
      laplacian (I := I)
          (LeviCivita (I := I) g) g rho x ≤
        2 * ((Module.finrank Real E - 1 : Nat) : Real) / r +
          ((Module.finrank Real E - 1 : Nat) : Real) * q := by
  classical
  dsimp only
  let r : Real := (_root_.Manifold.riemannianEDist I O x).toReal
  have hdist_ne : _root_.Manifold.riemannianEDist I O x ≠ 0 := by
    intro hzero
    exact hOx (riemannianEDist_eq_zero_imp_eq (I := I) O x hzero)
  have hr : 0 < r := by
    exact ENNReal.toReal_pos hdist_ne hfin
  obtain ⟨v, hexp, hlen⟩ :=
    minExp_of_ne_top (I := I) g hEnorm O x hfin
  obtain ⟨tail⟩ :=
    exists_calabiTail (I := I) g hEnorm v hexp hlen hr rfl
  refine ⟨tail, calabi_support_of_tail (I := I) g hEnorm q hq tail ?_⟩
  intro _
  dsimp only
  intro t ht
  exact hRic _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_calabiData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_calabiData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_calabiData ``Submission.DifferentialGeometry.exists_calabiData

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_calabiData_of_complete_metric
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (q : Real) (hq : 0 ≤ q)
    (hRic : Geometry.Riemannian.BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)))
    {O x : M} (hOx : O ≠ x)
    (hfin : riemannianEDistOf (I := I) g O x ≠ (⊤ : ENNReal)) :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    letI : TopologicalSpace.MetrizableSpace M :=
      Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : _root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M := inferInstance
    letI : CompleteSpace M := hcomplete.complete
    let hEnorm : IsMetricNorm (I := I) (M := M) g :=
      fun y v => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g y v
    let r := (_root_.Manifold.riemannianEDist I O x).toReal
    ∃ tail : CalabiTail (I := I) g hEnorm O x r,
      let rho : M → Real := fun y =>
        tail.initialLength + branchRadius (I := I) g tail.branch y
      ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
      rho x = r ∧
      (∀ᶠ y in 𝓝 x,
        (_root_.Manifold.riemannianEDist I O y).toReal ≤ rho y) ∧
      (∀ᶠ y in 𝓝 x,
        MDifferentiableAt I 𝓘(Real, Real) rho y) ∧
      MDifferentiableAt I (I.prod 𝓘(Real, E))
        (T% fun y : M => gradientFun (I := I) g rho y) x ∧
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) = 1 ∧
      laplacian (I := I)
          (LeviCivita (I := I) g) g rho x ≤
        2 * ((Module.finrank Real E - 1 : Nat) : Real) / r +
          ((Module.finrank Real E - 1 : Nat) : Real) * q := by
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let _ : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : _root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := inferInstance
  let _ : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro y v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g y v
  have hfin' : _root_.Manifold.riemannianEDist I O x ≠ (⊤ : ENNReal) := by
    simpa [riemannianEDistOf] using hfin
  exact exists_calabiData (I := I) (M := M) g hEnorm q hq hRic hOx hfin'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_calabiData_of_complete_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_calabiData_of_complete_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_calabiData_of_complete_metric ``Submission.DifferentialGeometry.exists_calabiData_of_complete_metric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem calabiDist_support
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (q : Real) (hq : 0 ≤ q)
    (hRic : Geometry.Riemannian.BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)))
    {O x : M} (hOx : O ≠ x)
    (hfin : _root_.Manifold.riemannianEDist I O x ≠ (⊤ : ENNReal)) :
    let r := (_root_.Manifold.riemannianEDist I O x).toReal
    ∃ rho : M → Real,
      ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
      rho x = r ∧
      (∀ᶠ y in 𝓝 x,
        (_root_.Manifold.riemannianEDist I O y).toReal ≤ rho y) ∧
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) ≤ 1 ∧
      laplacian (I := I)
          (LeviCivita (I := I) g) g rho x ≤
        2 * ((Module.finrank Real E - 1 : Nat) : Real) / r +
          ((Module.finrank Real E - 1 : Nat) : Real) * q := by
  dsimp only
  obtain ⟨tail, hrho_inf, hrho_x, hupper, _hrho_ev, _hrho_grad,
      hgrad_norm, hlap⟩ :=
    exists_calabiData (I := I) g hEnorm q hq hRic hOx hfin
  exact
    ⟨fun y => tail.initialLength + branchRadius (I := I) g tail.branch y,
      hrho_inf, hrho_x, hupper, hgrad_norm.le, hlap⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.calabiDist_support then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.calabiDist_support"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.calabiDist_support ``Submission.DifferentialGeometry.calabiDist_support

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem calabiDist_support_of_complete_metric
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (q : Real) (hq : 0 ≤ q)
    (hRic : Geometry.Riemannian.BonnetMyers.RicciBoundedBelow (I := I) g
      (-(((Module.finrank Real E - 1 : Nat) : Real) * q ^ 2)))
    {O x : M} (hOx : O ≠ x)
    (hfin : riemannianEDistOf (I := I) g O x ≠ (⊤ : ENNReal)) :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    letI : TopologicalSpace.MetrizableSpace M :=
      Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : _root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M := inferInstance
    letI : CompleteSpace M := hcomplete.complete
    let r := (_root_.Manifold.riemannianEDist I O x).toReal
    ∃ rho : M → Real,
      ContMDiffAt I 𝓘(Real, Real) ∞ rho x ∧
      rho x = r ∧
      (∀ᶠ y in 𝓝 x,
        (_root_.Manifold.riemannianEDist I O y).toReal ≤ rho y) ∧
      g.inner x
          (gradientFun (I := I) g rho x)
          (gradientFun (I := I) g rho x) ≤ 1 ∧
      laplacian (I := I)
          (LeviCivita (I := I) g) g rho x ≤
        2 * ((Module.finrank Real E - 1 : Nat) : Real) / r +
          ((Module.finrank Real E - 1 : Nat) : Real) * q := by
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let _ : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let _ : T3Space M := inferInstance
  let _ : _root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro y v w; rfl⟩⟩
  let _ : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace M := inferInstance
  let _ : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro y v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g y v
  have hfin' : _root_.Manifold.riemannianEDist I O x ≠ (⊤ : ENNReal) := by
    simpa [riemannianEDistOf] using hfin
  exact calabiDist_support (I := I) (M := M) g hEnorm q hq hRic hOx hfin'

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.calabiDist_support_of_complete_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.calabiDist_support_of_complete_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.calabiDist_support_of_complete_metric ``Submission.DifferentialGeometry.calabiDist_support_of_complete_metric

private theorem continuousAt_fiber_smul
    {X B F : Type*} [TopologicalSpace X] [TopologicalSpace B]
    [NormedAddCommGroup F] [NormedSpace Real F]
    {V : B → Type*} [∀ b, AddCommGroup (V b)] [∀ b, Module Real (V b)]
    [∀ b, TopologicalSpace (V b)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F V)] [FiberBundle F V] [VectorBundle Real F V]
    {b : X → B} {v : ∀ x, V (b x)} {a : X → Real} {x₀ : X}
    (hv : ContinuousAt (fun x => TotalSpace.mk' F (b x) (v x)) x₀)
    (ha : ContinuousAt a x₀) :
    ContinuousAt (fun x => TotalSpace.mk' F (b x) (a x • v x)) x₀ := by
  rw [FiberBundle.continuousAt_totalSpace] at hv ⊢
  refine ⟨hv.1, ?_⟩
  let e := _root_.FiberBundle.trivializationAt F V (b x₀)
  have hb : ∀ᶠ x in 𝓝 x₀, b x ∈ e.baseSet :=
    hv.1 (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (b x₀)))
  have heq :
      (fun x => (e (TotalSpace.mk' F (b x) (a x • v x))).2) =ᶠ[𝓝 x₀]
        fun x => a x • (e (TotalSpace.mk' F (b x) (v x))).2 := by
    filter_upwards [hb] with x hx
    exact (e.linear Real hx).map_smul (a x) (v x)
  exact (ha.smul hv.2).congr_of_eventuallyEq heq

run_cmd do
  let target := ``Submission.DifferentialGeometry.continuousAt_fiber_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.continuousAt_fiber_smul target :: scope.openDecls } }

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless]
  [T2Space M]
  [SigmaCompactSpace M] in
theorem edistOf_le_arcLength
    (g : SmoothRiemannianMetric I M) {γ : Real → M} {a b : Real}
    (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc a b)) :
    riemannianEDistOf (I := I) g (γ a) (γ b) ≤
      ENNReal.ofReal
        (Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) := by
  let _ : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  change _root_.Manifold.riemannianEDist I (γ a) (γ b) ≤ _
  apply Geometry.Riemannian.Geodesic.riemannianEDist_le_arcLength
    (I := I) g hab hγ
  intro t ht
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  congr 2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.edistOf_le_arcLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.edistOf_le_arcLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.edistOf_le_arcLength ``Submission.DifferentialGeometry.edistOf_le_arcLength

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless]
  [T2Space M]
  [SigmaCompactSpace M] in
theorem edistOf_le_two_arcs
    (g : SmoothRiemannianMetric I M)
    {γ δ : Real → M} {a b c d : Real}
    (hab : a ≤ b) (hcd : c ≤ d)
    (hγ : ContMDiffOn 𝓘(Real, Real) I 1 γ (Set.Icc a b))
    (hδ : ContMDiffOn 𝓘(Real, Real) I 1 δ (Set.Icc c d))
    (hjoin : γ b = δ c) :
    riemannianEDistOf (I := I) g (γ a) (δ d) ≤
      ENNReal.ofReal
          (Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) +
        ENNReal.ofReal
          (Geometry.Riemannian.Variation.arcLength (I := I) g δ c d) := by
  let _ : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  change _root_.Manifold.riemannianEDist I (γ a) (δ d) ≤ _
  calc
    _root_.Manifold.riemannianEDist I (γ a) (δ d) ≤
        _root_.Manifold.riemannianEDist I (γ a) (γ b) +
          riemannianEDist I (γ b) (δ d) :=
      Manifold.riemannianEDist_triangle
    _ = _root_.Manifold.riemannianEDist I (γ a) (γ b) +
          riemannianEDist I (δ c) (δ d) := by rw [hjoin]
    _ ≤ ENNReal.ofReal
          (Geometry.Riemannian.Variation.arcLength (I := I) g γ a b) +
        ENNReal.ofReal
          (Geometry.Riemannian.Variation.arcLength (I := I) g δ c d) :=
      add_le_add
        (edistOf_le_arcLength (I := I) g hab hγ)
        (edistOf_le_arcLength (I := I) g hcd hδ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.edistOf_le_two_arcs then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.edistOf_le_two_arcs"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.edistOf_le_two_arcs ``Submission.DifferentialGeometry.edistOf_le_two_arcs

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem calabi_tail_of
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (O x : M) (hOx : _root_.Manifold.riemannianEDist I O x ≠ ⊤)
    (B : DiagonalInverseBranch (I := I) g hEnorm x) :
    ∃ (v : TangentSpace I O) (s₀ : Real),
      expMapIntrinsic (I := I) g hEnorm O v = x ∧
      Real.sqrt (g.inner O v v) = (_root_.Manifold.riemannianEDist I O x).toReal ∧
      0 < s₀ ∧ s₀ < 1 ∧
      let velocity : Real → TangentBundle I M :=
        intrinsicVelocityLift (I := I) g hEnorm O v
      let tail : Real → TangentBundle I M := fun s =>
        ⟨(velocity s).proj, (1 - s) • (velocity s).snd⟩
      tail s₀ ∈ B.hom.source ∧
        ((tail s₀).proj, x) ∈ B.dom ∧
        expMapIntrinsic (I := I) g hEnorm (tail s₀).proj (tail s₀).snd = x ∧
        B.inv ((tail s₀).proj, x) = tail s₀ := by
  obtain ⟨v, hvx, hvmin⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top
      (I := I) g hEnorm O x hOx
  let velocity : Real → TangentBundle I M :=
    intrinsicVelocityLift (I := I) g hEnorm O v
  let tail : Real → TangentBundle I M := fun s =>
    ⟨(velocity s).proj, (1 - s) • (velocity s).snd⟩
  have hvelocity : Continuous velocity :=
    (lift_isIntegral (I := I) g hEnorm O v).continuous
  have htail : ContinuousAt tail 1 := by
    apply continuousAt_fiber_smul hvelocity.continuousAt
    fun_prop
  have hvelocity_one : (velocity 1).proj = x := by
    change intrinsicGeodesic (I := I) g hEnorm O v 1 = x
    simpa only [expMapIntrinsic_def] using hvx
  have htail_one :
      tail 1 = (⟨x, (0 : TangentSpace I x)⟩ : TangentBundle I M) := by
    apply TotalSpace.ext hvelocity_one
    apply heq_of_eq
    simp only [tail, sub_self, zero_smul]
    rfl
  have htail_mem : tail 1 ∈ B.hom.source := by
    rw [htail_one]
    exact B.zero_mem
  have hsource_nhds : {s : Real | tail s ∈ B.hom.source} ∈ 𝓝 (1 : Real) :=
    htail.preimage_mem_nhds (B.hom.open_source.mem_nhds htail_mem)
  obtain ⟨ε, hε, hε_sub⟩ := Metric.mem_nhds_iff.mp hsource_nhds
  let d : Real := _root_.Min.min ε 1 / 2
  let s₀ : Real := 1 - d
  have hd_pos : 0 < d := by
    dsimp [d]
    exact half_pos (lt_min hε zero_lt_one)
  have hd_lt_one : d < 1 := by
    dsimp [d]
    nlinarith [min_le_right ε (1 : Real)]
  have hd_lt_ε : d < ε := by
    dsimp [d]
    nlinarith [min_le_left ε (1 : Real), lt_min hε zero_lt_one]
  have hs₀_pos : 0 < s₀ := by
    dsimp [s₀]
    linarith
  have hs₀_lt : s₀ < 1 := by
    dsimp [s₀]
    linarith
  have hs₀_ball : s₀ ∈ Metric.ball (1 : Real) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have : |s₀ - 1| = d := by
      dsimp [s₀]
      rw [abs_of_nonpos]
      · ring
      · linarith
    rw [this]
    exact hd_lt_ε
  have hs₀_source : tail s₀ ∈ B.hom.source := hε_sub hs₀_ball
  have hs₀_exp :
      expMapIntrinsic (I := I) g hEnorm (tail s₀).proj (tail s₀).snd = x := by
    have hcontinue :=
      congrFun (intrinsicGeodesic_continuation (I := I) g hEnorm O v s₀) (1 - s₀)
    have hend :
        intrinsicGeodesic (I := I) g hEnorm O v 1 = x := by
      simpa only [expMapIntrinsic_def] using hvx
    change intrinsicGeodesic (I := I) g hEnorm (velocity s₀).proj
      ((1 - s₀) • (velocity s₀).snd) 1 = x
    rw [intrinsicGeodesic_smul (I := I) g hEnorm]
    rw [show (velocity s₀).proj =
        intrinsicGeodesic (I := I) g hEnorm O v s₀ by
          exact Geometry.Riemannian.Exponential.velocityLift_proj
            (I := I) g hEnorm O v s₀]
    rw [show (velocity s₀).snd =
        (mfderiv 𝓘(Real, Real) I
          (intrinsicGeodesic (I := I) g hEnorm O v) s₀ :
            Real →L[Real] TangentSpace I
              (intrinsicGeodesic (I := I) g hEnorm O v s₀)) 1 by rfl]
    calc
      intrinsicGeodesic (I := I) g hEnorm
          (intrinsicGeodesic (I := I) g hEnorm O v s₀)
          (mfderiv 𝓘(Real, Real) I
            (intrinsicGeodesic (I := I) g hEnorm O v) s₀ 1)
          (1 - s₀) =
          intrinsicGeodesic (I := I) g hEnorm O v (1 - s₀ + s₀) :=
        hcontinue.symm
      _ = intrinsicGeodesic (I := I) g hEnorm O v 1 := by
        congr 1
        ring
      _ = x := hend
  have hs₀_dom : ((tail s₀).proj, x) ∈ B.dom := by
    have hmap : B.hom (tail s₀) ∈ B.hom.target :=
      B.hom.map_source hs₀_source
    have hhom : B.hom (tail s₀) = ((tail s₀).proj, x) := by
      have hdiag :
          diagExp (I := I) g hEnorm (tail s₀) = ((tail s₀).proj, x) := by
        change ((tail s₀).proj,
          expMapIntrinsic (I := I) g hEnorm (tail s₀).proj (tail s₀).snd) =
            ((tail s₀).proj, x)
        rw [hs₀_exp]
      change (fun u ↦ B.hom u) (tail s₀) = ((tail s₀).proj, x)
      exact (B.hom_eq hs₀_source).trans hdiag
    change ((tail s₀).proj, x) ∈ B.hom.target
    rwa [← hhom]
  refine ⟨v, s₀, hvx, hvmin, hs₀_pos, hs₀_lt, ?_⟩
  dsimp only
  refine ⟨hs₀_source, hs₀_dom, hs₀_exp, ?_⟩
  exact B.inv_eq_of_exp hs₀_source hs₀_exp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.calabi_tail_of then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.calabi_tail_of"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.calabi_tail_of ``Submission.DifferentialGeometry.calabi_tail_of

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_calabi_tail
    [_root_.Bundle.RiemannianBundle (fun y : M => TangentSpace I y)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (O x : M) (hOx : _root_.Manifold.riemannianEDist I O x ≠ ⊤) :
    ∃ (v : TangentSpace I O) (s₀ : Real),
      expMapIntrinsic (I := I) g hEnorm O v = x ∧
      Real.sqrt (g.inner O v v) = (_root_.Manifold.riemannianEDist I O x).toReal ∧
      0 < s₀ ∧ s₀ < 1 ∧
      let velocity : Real → TangentBundle I M :=
        intrinsicVelocityLift (I := I) g hEnorm O v
      let tail : Real → TangentBundle I M := fun s =>
        ⟨(velocity s).proj, (1 - s) • (velocity s).snd⟩
      tail s₀ ∈
          (Geometry.Riemannian.Exponential.standardDiagonalInverseBranch
            (I := I) g hEnorm x).hom.source ∧
        ((tail s₀).proj, x) ∈
          (Geometry.Riemannian.Exponential.standardDiagonalInverseBranch
            (I := I) g hEnorm x).dom ∧
        expMapIntrinsic (I := I) g hEnorm (tail s₀).proj (tail s₀).snd = x ∧
        (Geometry.Riemannian.Exponential.standardDiagonalInverseBranch
          (I := I) g hEnorm x).inv
          ((tail s₀).proj, x) = tail s₀ := by
  exact calabi_tail_of (I := I) g hEnorm O x hOx
    (Geometry.Riemannian.Exponential.standardDiagonalInverseBranch (I := I) g hEnorm x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.exists_calabi_tail then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.exists_calabi_tail"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.exists_calabi_tail ``Submission.DifferentialGeometry.exists_calabi_tail

end DifferentialGeometry
