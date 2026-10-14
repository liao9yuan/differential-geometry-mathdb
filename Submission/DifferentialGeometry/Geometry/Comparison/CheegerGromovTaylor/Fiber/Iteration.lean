import Submission.DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.Core.JensenConvexity
import Submission.DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.Fiber.Basic
import Submission.DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.Paths.Radial
import Submission.DifferentialGeometry.Geometry.Exponential.NormalCoordinates.LoopTransport

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Metric _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CheegerGromovTaylor

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Variation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

noncomputable local instance _root_.Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.instSigmaCompactSpaceSubtypeMemOpensIntrinsicPullBall_5 {R : Real} :
    SigmaCompactSpace (intrinsicPullBall (E := E) R) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen
      𝓘(Real, E) (intrinsicPullBall (E := E) R).isOpen)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.instSigmaCompactSpaceSubtypeMemOpensIntrinsicPullBall_5 then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.instSigmaCompactSpaceSubtypeMemOpensIntrinsicPullBall_5"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.instSigmaCompactSpaceSubtypeMemOpensIntrinsicPullBall_5 ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.instSigmaCompactSpaceSubtypeMemOpensIntrinsicPullBall_5

noncomputable def loopRadial
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (c : Path p p) (z : E) :
    Path p (intrinsicFramedExp (I := I) g hEnorm p z) :=
  c.trans (radialFlat (I := I) g hEnorm p z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial

theorem loopRadial_flat
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c) (z : E) :
    Path.IsContMDiffWithSittingInstants (I := I) 1 (loopRadial (I := I) g hEnorm p c z) :=
  hc.trans (radialFlat_flat (I := I) g hEnorm p z)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial_flat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial_flat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial_flat ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial_flat

theorem loopRadial_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c) (z : E) :
    Path.riemannianELength (I := I) (loopRadial (I := I) g hEnorm p c z) =
      Path.riemannianELength (I := I) c + ENNReal.ofReal ‖z‖ := by
  rw [loopRadial, Path.riemannianELength_trans
    (hc.contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero)
    ((radialFlat_flat (I := I) g hEnorm p z).contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero),
    radialFlat_len (I := I) g hEnorm p z]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial_len then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial_len"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial_len ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial_len

theorem loopRadial_len_lt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    {z : E} (hz : ‖z‖ ≤ a) :
    Path.riemannianELength (I := I) (loopRadial (I := I) g hEnorm p c z) <
      ENNReal.ofReal (L + a) := by
  rw [loopRadial_len (I := I) g hEnorm p c hc z]
  calc
    Path.riemannianELength (I := I) c + ENNReal.ofReal ‖z‖ <
        ENNReal.ofReal L + ENNReal.ofReal a :=
      ENNReal.add_lt_add_of_lt_of_le ENNReal.ofReal_ne_top
        hcLen (ENNReal.ofReal_le_ofReal hz)
    _ = ENNReal.ofReal (L + a) := (ENNReal.ofReal_add hL ha).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial_len_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial_len_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial_len_lt ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopRadial_len_lt

theorem exists_loopLift
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (z : intrinsicPullBall (E := E) R)
    (hz : z ∈ intrinsicCore (E := E) R a) :
    Nonempty
      (IntrinsicFrameLift (I := I) g hEnorm p
        (loopRadial (I := I) g hEnorm p c (z : E)).extend 0 1) := by
  have hR : 0 < R := (add_nonneg hL ha).trans_lt hfit
  have hlenLa :=
    loopRadial_len_lt (I := I) g hEnorm p hL ha c hc hcLen hz
  have hlenR :
      Path.riemannianELength (I := I) (loopRadial (I := I) g hEnorm p c (z : E)) <
        ENNReal.ofReal R :=
    hlenLa.trans ((ENNReal.ofReal_lt_ofReal_iff hR).2 hfit)
  exact exists_intr_lift (I := I) g hEnorm p zero_le_one
    (loopRadial_flat (I := I) g hEnorm p c hc (z : E)).contMDiff.contMDiffOn
    (by simp only [Path.extend_zero, loopRadial])
    hlenR hloc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.exists_loopLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.exists_loopLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.exists_loopLift ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.exists_loopLift

noncomputable def loopTransportLift
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (z : intrinsicPullBall (E := E) R)
    (hz : z ∈ intrinsicCore (E := E) R a) :
    IntrinsicFrameLift (I := I) g hEnorm p
      (loopRadial (I := I) g hEnorm p c (z : E)).extend 0 1 :=
  Classical.choice
    (exists_loopLift (I := I) g hEnorm p hL ha hfit hloc c hc hcLen z hz)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportLift ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportLift

noncomputable def loopTransport
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (z : intrinsicPullBall (E := E) R)
    (hz : z ∈ intrinsicCore (E := E) R a) :
    intrinsicPullBall (E := E) R := by
  let P :=
    loopTransportLift (I := I) g hEnorm p hL ha hfit hloc c hc hcLen z hz
  refine ⟨P.toFun 1, ?_⟩
  change P.toFun 1 ∈ Metric.ball (0 : E) R
  have hR : 0 < R := (add_nonneg hL ha).trans_lt hfit
  have hlenLa :=
    loopRadial_len_lt (I := I) g hEnorm p hL ha c hc hcLen hz
  have hlenR :
      Path.riemannianELength (I := I) (loopRadial (I := I) g hEnorm p c (z : E)) <
        ENNReal.ofReal R :=
    hlenLa.trans ((ENNReal.ofReal_lt_ofReal_iff hR).2 hfit)
  simpa only [Metric.mem_ball, dist_zero_right] using
    P.norm_lt hR hlenR ⟨zero_le_one, le_rfl⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport

noncomputable def loopTransportExt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (z : intrinsicPullBall (E := E) R) :
    intrinsicPullBall (E := E) R := by
  classical
  exact
    if hz : z ∈ intrinsicCore (E := E) R a then
      loopTransport (I := I) g hEnorm p hL ha hfit hloc
        c hc hcLen z hz
    else z

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportExt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportExt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportExt ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportExt

theorem loopTransportExt_eq
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (z : intrinsicPullBall (E := E) R)
    (hz : z ∈ intrinsicCore (E := E) R a) :
    loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
        c hc hcLen z =
      loopTransport (I := I) g hEnorm p hL ha hfit hloc
        c hc hcLen z hz := by
  simp only [loopTransportExt, dif_pos hz]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportExt_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportExt_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportExt_eq ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportExt_eq

theorem loopTransport_exp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (z : intrinsicPullBall (E := E) R)
    (hz : z ∈ intrinsicCore (E := E) R a) :
    intrinsicFramedExp (I := I) g hEnorm p
        (loopTransport (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen z hz : E) =
      intrinsicFramedExp (I := I) g hEnorm p (z : E) := by
  let P :=
    loopTransportLift (I := I) g hEnorm p hL ha hfit hloc c hc hcLen z hz
  have hP := P.lifts (show (1 : Real) ∈ Set.Icc 0 1 by exact ⟨zero_le_one, le_rfl⟩)
  simpa only [loopTransport, P, Function.comp_apply, Path.extend_one,
    loopRadial] using hP

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_exp ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_exp

theorem loopTransportExt_exp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (z : intrinsicPullBall (E := E) R) :
    intrinsicFramedExp (I := I) g hEnorm p
        (loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen z : E) =
      intrinsicFramedExp (I := I) g hEnorm p (z : E) := by
  classical
  by_cases hz : z ∈ intrinsicCore (E := E) R a
  · rw [loopTransportExt_eq (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen z hz]
    exact loopTransport_exp (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen z hz
  · simp only [loopTransportExt, dif_neg hz]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportExt_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportExt_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportExt_exp ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransportExt_exp

theorem loopIter_exp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (n : Nat) (z : intrinsicPullBall (E := E) R) :
    intrinsicFramedExp (I := I) g hEnorm p
        (((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen)^[n]) z : E) =
      intrinsicFramedExp (I := I) g hEnorm p (z : E) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact
        (loopTransportExt_exp (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen
          (((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
            c hc hcLen)^[n]) z)).trans ih

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopIter_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopIter_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopIter_exp ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopIter_exp

theorem intrinsicIter_exp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hR : 0 < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (n : Nat) :
    intrinsicFramedExp (I := I) g hEnorm p
        (((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen)^[n]) (intrinsicZero (E := E) hR) : E) =
      p := by
  calc
    intrinsicFramedExp (I := I) g hEnorm p
        (((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen)^[n]) (intrinsicZero (E := E) hR) : E) =
        intrinsicFramedExp (I := I) g hEnorm p
          (intrinsicZero (E := E) hR : E) :=
      loopIter_exp (I := I) g hEnorm p hL ha hfit hloc
        c hc hcLen n (intrinsicZero (E := E) hR)
    _ = p := by
      rw [intrinsicFrame_apply, intrinsicZero, map_zero,
        expMapIntrinsic_zero (I := I) g hEnorm p]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_exp ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_exp

theorem loopTransport_norm
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (z : intrinsicPullBall (E := E) R)
    (hz : z ∈ intrinsicCore (E := E) R a) :
    ‖(loopTransport (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen z hz : E)‖ < L + ‖(z : E)‖ := by
  let P :=
    loopTransportLift (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen z hz
  have hLpos : 0 < L := by
    exact ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hcLen)
  have hsumPos : 0 < L + ‖(z : E)‖ :=
    lt_of_lt_of_le hLpos (le_add_of_nonneg_right (norm_nonneg _))
  have hlen :
      Path.riemannianELength (I := I) (loopRadial (I := I) g hEnorm p c (z : E)) <
        ENNReal.ofReal (L + ‖(z : E)‖) := by
    rw [loopRadial_len (I := I) g hEnorm p c hc (z : E)]
    calc
      Path.riemannianELength (I := I) c + ENNReal.ofReal ‖(z : E)‖ <
          ENNReal.ofReal L + ENNReal.ofReal ‖(z : E)‖ :=
        ENNReal.add_lt_add_right ENNReal.ofReal_ne_top hcLen
      _ = ENNReal.ofReal (L + ‖(z : E)‖) :=
        (ENNReal.ofReal_add hL (norm_nonneg _)).symm
  simpa only [loopTransport, P] using
    P.norm_lt hsumPos hlen
      (show (1 : Real) ∈ Set.Icc 0 1 by exact ⟨zero_le_one, le_rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_norm ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_norm

theorem loopTransport_bound
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (z : intrinsicPullBall (E := E) R)
    (hz : z ∈ intrinsicCore (E := E) R a) :
    ‖(loopTransport (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen z hz : E)‖ < L + a := by
  let P :=
    loopTransportLift (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen z hz
  have hLpos : 0 < L := by
    exact ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hcLen)
  have hLa : 0 < L + a := lt_of_lt_of_le hLpos (le_add_of_nonneg_right ha)
  have hlen :=
    loopRadial_len_lt (I := I) g hEnorm p hL ha c hc hcLen hz
  simpa only [loopTransport, P] using
    P.norm_lt hLa hlen
      (show (1 : Real) ∈ Set.Icc 0 1 by exact ⟨zero_le_one, le_rfl⟩)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_bound ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_bound

theorem intrinsicIter_norm
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hR : 0 < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (n : Nat) (hna : (n : Real) * L < a) :
    ‖(((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen)^[n]) (intrinsicZero (E := E) hR) : E)‖ ≤
      (n : Real) * L := by
  let T : intrinsicPullBall (E := E) R → intrinsicPullBall (E := E) R :=
    loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen
  let z₀ := intrinsicZero (E := E) hR
  change ‖((T^[n]) z₀ : E)‖ ≤ (n : Real) * L
  induction n with
  | zero =>
      simp only [Function.iterate_zero_apply, Nat.cast_zero, _root_.MulZeroClass.zero_mul,
        z₀, intrinsicZero, norm_zero, le_rfl]
  | succ n ih =>
      have hnCast : (n : Real) ≤ (n.succ : Nat) := by
        exact_mod_cast Nat.le_succ n
      have hnMul : (n : Real) * L ≤ (n.succ : Real) * L :=
        mul_le_mul_of_nonneg_right hnCast hL
      have hna' : (n : Real) * L < a :=
        lt_of_le_of_lt hnMul hna
      have hnNorm : ‖((T^[n]) z₀ : E)‖ ≤ (n : Real) * L :=
        ih hna'
      let z := (T^[n]) z₀
      have hz : z ∈ intrinsicCore (E := E) R a := by
        rw [mem_intrCore]
        exact hnNorm.trans (le_of_lt hna')
      rw [Function.iterate_succ_apply']
      calc
        ‖(T z : E)‖ =
            ‖(loopTransport (I := I) g hEnorm p hL ha hfit hloc
              c hc hcLen z hz : E)‖ := by
          change
            ‖(loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
              c hc hcLen z : E)‖ =
              ‖(loopTransport (I := I) g hEnorm p hL ha hfit hloc
                c hc hcLen z hz : E)‖
          rw [loopTransportExt_eq (I := I) g hEnorm p hL ha hfit hloc
            c hc hcLen z hz]
        _ ≤ L + ‖(z : E)‖ :=
          (loopTransport_norm (I := I) g hEnorm p hL ha hfit hloc
            c hc hcLen z hz).le
        _ ≤ L + (n : Real) * L := by
          linarith
        _ = (n.succ : Real) * L := by
          push_cast
          ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_norm then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_norm"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_norm ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_norm

theorem loopTransport_maps
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L) :
    _root_.Set.MapsTo
      (fun z : {z : intrinsicPullBall (E := E) R //
          z ∈ intrinsicCore (E := E) R a} =>
        loopTransport (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen z.1 z.2)
      Set.univ (intrinsicCore (E := E) R (L + a)) := by
  intro z _
  rw [mem_intrCore]
  exact (loopTransport_bound (I := I) g hEnorm p hL ha hfit hloc
    c hc hcLen z.1 z.2).le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_maps then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_maps"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_maps ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_maps

private theorem framed_exp_eq
    (g : SmoothRiemannianMetric I M) (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v))) (p : M) :
    framedExpMap g p = intrinsicFramedExp g hEnorm p := by
  funext z
  rw [framedExpMap_apply, intrinsicFrame_apply, expMap_eq_expMapIntrinsic g hEnorm p]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.framed_exp_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.framed_exp_eq target :: scope.openDecls } }

omit [NeZero (Module.finrank Real E)] in
private theorem complete_domain
    (g : SmoothRiemannianMetric I M) (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v))) (p : M) (R : ℝ) :
    MapsTo (normalFrame g p) (Metric.ball (0 : E) R) (expDomain g p) := by
  rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
  exact _root_.Set.mapsTo_univ _ _

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.complete_domain
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.complete_domain target :: scope.openDecls } }

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private theorem length_eq_metric
    (g : SmoothRiemannianMetric I M) (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v))) (p : M)
    (c : Path p p) (hc : c.IsContMDiffWithSittingInstants (I := I) 1) :
    c.riemannianELength (I := I) =
      (let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
        c.riemannianELength (I := I)) := by
  have hint := Geodesic.speedSqrt_integrableOn_Icc_of_C1 g zero_le_one hc.contMDiff.contMDiffOn
  have hOld := Geodesic.pathELength_eq_arcLength_of_enorm_eq g zero_le_one
    (hint.mono_set _root_.Set.Ioo_subset_Icc_self) (fun t _ => hEnorm (c.extend t) _)
  let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hn : IsMetricNorm g := by
    intro x v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hNew := Geodesic.pathELength_eq_arcLength_of_enorm_eq g zero_le_one
    (hint.mono_set _root_.Set.Ioo_subset_Icc_self) (fun t _ => hn (c.extend t) _)
  exact hOld.trans hNew.symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.length_eq_metric
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.length_eq_metric target :: scope.openDecls } }

omit [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
    [T2Space M] [SigmaCompactSpace M] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] in
private theorem transport_budget
    (g : SmoothRiemannianMetric I M) (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v))) (p : M)
    {R L a : ℝ} (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (c : Path p p) (hc : c.IsContMDiffWithSittingInstants (I := I) 1)
    (hcLen : c.riemannianELength (I := I) < ENNReal.ofReal L)
    (z : intrinsicPullBall (E := E) R) (hz : z ∈ intrinsicCore (E := E) R a) :
    let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    c.riemannianELength (I := I) + ENNReal.ofReal ‖(z : E)‖ < ENNReal.ofReal R := by
  change (let : _root_.Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
    c.riemannianELength (I := I)) + ENNReal.ofReal ‖(z : E)‖ < ENNReal.ofReal R
  rw [← length_eq_metric g hEnorm p c hc]
  calc
    c.riemannianELength (I := I) + ENNReal.ofReal ‖(z : E)‖ <
        ENNReal.ofReal L + ENNReal.ofReal a :=
      ENNReal.add_lt_add_of_lt_of_le ENNReal.ofReal_ne_top hcLen
        (ENNReal.ofReal_le_ofReal hz)
    _ = ENNReal.ofReal (L + a) := (ENNReal.ofReal_add hL ha).symm
    _ < ENNReal.ofReal R :=
      (ENNReal.ofReal_lt_ofReal_iff ((add_nonneg hL ha).trans_lt hfit)).mpr hfit

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.transport_budget
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.transport_budget target :: scope.openDecls } }

private theorem transport_eq
    (g : SmoothRiemannianMetric I M) (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : ℝ} (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (intrinsicFramedExp g hEnorm p) (Metric.ball (0 : E) R))
    (c : Path p p) (hc : c.IsContMDiffWithSittingInstants (I := I) 1)
    (hcLen : c.riemannianELength (I := I) < ENNReal.ofReal L)
    (z : intrinsicPullBall (E := E) R) (hz : z ∈ intrinsicCore (E := E) R a) :
    CheegerGromovTaylor.loopTransport g hEnorm p hL ha hfit hloc c hc hcLen z hz =
      NormalCoordinates.loopTransport g p (complete_domain g hEnorm p R)
        (by rw [framed_exp_eq g hEnorm p]; exact hloc) c hc z
        (transport_budget g hEnorm p hL ha hfit c hc hcLen z hz) := by
  let P := loopTransportLift g hEnorm p hL ha hfit hloc c hc hcLen z hz
  have hR : 0 < R := (add_nonneg hL ha).trans_lt hfit
  have hlen : (loopRadial g hEnorm p c (z : E)).riemannianELength (I := I) <
      ENNReal.ofReal R :=
    (loopRadial_len_lt g hEnorm p hL ha c hc hcLen hz).trans
      ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hfit)
  apply Subtype.ext
  unfold NormalCoordinates.loopTransport
  dsimp only
  generalize_proofs _ _ hLift
  have hNew := Classical.choose_spec hLift
  have hOld : isLiftOn (framedExpMap g p)
      (loopRadial g hEnorm p c (z : E)).extend (Metric.ball (0 : E) R) 0 0 1 P.toFun := by
    rw [framed_exp_eq g hEnorm p]
    exact ⟨P.contDiff.continuousOn, P.start,
      fun t ht => ⟨P.maps_ball hR hlen ht, P.lifts ht⟩⟩
  have hpath : (loopRadial g hEnorm p c (z : E)).extend =
      (c.trans (radialPath g p (normalFrame g p (z : E))
        ((complete_domain g hEnorm p R) z.property)).withSittingInstants).extend := by
    ext t
    change (c.trans (radialFlat g hEnorm p (z : E))).extend t = _
    by_cases ht : t ≤ 1 / 2
    · rw [Path.extend_trans_of_le_half _ _ ht, Path.extend_trans_of_le_half _ _ ht]
    · rw [Path.extend_trans_of_half_le _ _ (not_le.mp ht).le,
        Path.extend_trans_of_half_le _ _ (not_le.mp ht).le, radialFlat_extend,
        extend_radialPath_withSittingInstants]
      simp only [intrinsicFrame_apply, map_smul, expMap_eq_expMapIntrinsic g hEnorm p]
      rfl
  have hOld' : isLiftOn (framedExpMap g p)
      (c.trans (radialPath g p (normalFrame g p (z : E))
        ((complete_domain g hEnorm p R) z.property)).withSittingInstants).extend
      (Metric.ball (0 : E) R) 0 0 1 P.toFun :=
    ⟨hOld.continuousOn, hOld.2.1, fun t ht =>
      ⟨hOld.mapsTo ht, (hOld.2.2 t ht).2.trans (DFunLike.congr_fun hpath t)⟩⟩
  exact hOld'.eqOn zero_le_one Metric.isOpen_ball
    (by rw [framed_exp_eq g hEnorm p]; exact hloc) hNew ⟨zero_le_one, le_rfl⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.transport_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.transport_eq target :: scope.openDecls } }


private theorem pull_metric_eq
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : ℝ}
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (intrinsicFramedExp g hEnorm p) (Metric.ball (0 : E) R)) :
    intrinsicPullMetric g hEnorm p hloc =
      localPullMetric g (fun z : intrinsicPullBall (E := E) R => framedExpMap g p z)
        (isLocalDiffeomorph_restrict_open (intrinsicPullBall (E := E) R)
          (by rw [framed_exp_eq g hEnorm p]; exact hloc)) := by
  have hf : intrinsicExpOn g hEnorm p R =
      fun z : intrinsicPullBall (E := E) R => framedExpMap g p z := by
    funext z
    exact (congrFun (framed_exp_eq g hEnorm p) (z : E)).symm
  change localPullMetric g (intrinsicExpOn g hEnorm p R)
    (intrinsicExpOn_local g hEnorm p hloc) = _
  simp only [hf]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.pull_metric_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.pull_metric_eq target :: scope.openDecls } }

theorem loopTransport_cont
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L) :
    Continuous
      (fun z : {z : intrinsicPullBall (E := E) R //
          z ∈ intrinsicCore (E := E) R a} =>
        loopTransport (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen z.1 z.2) := by
  have hn := NormalCoordinates.continuous_loopTransport g p (complete_domain g hEnorm p R)
    (by rw [framed_exp_eq g hEnorm p]; exact hloc) c hc (intrinsicCore (E := E) R a)
    (fun z hz => transport_budget g hEnorm p hL ha hfit c hc hcLen z hz)
  apply hn.congr
  intro z
  exact (transport_eq g hEnorm p hL ha hfit hloc c hc hcLen z.1 z.2).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_cont ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_cont

theorem loopTransport_curve
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    {γ : Real → intrinsicPullBall (E := E) R} {s t : Real}
    (hγ :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ (Set.Icc s t))
    (hγcore : ∀ u : Real, γ u ∈ intrinsicCore (E := E) R a) :
    letI : _root_.Bundle.RiemannianBundle
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨(intrinsicPullMetric (I := I) g hEnorm p hloc).toRiemannianMetric⟩
    let η : Real → intrinsicPullBall (E := E) R :=
      fun u =>
        loopTransport (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen (γ u) (hγcore u)
    ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 η (Set.Icc s t) ∧
      Manifold.pathELength 𝓘(Real, E) η s t =
        Manifold.pathELength 𝓘(Real, E) γ s t := by
  have hcont := NormalCoordinates.contMDiffOn_loopTransport_comp g p
    (complete_domain g hEnorm p R) (by rw [framed_exp_eq g hEnorm p]; exact hloc) c hc hγ
    (fun u => transport_budget g hEnorm p hL ha hfit c hc hcLen (γ u) (hγcore u))
  have hlen := NormalCoordinates.pathELength_loopTransport_comp g p
    (complete_domain g hEnorm p R) (by rw [framed_exp_eq g hEnorm p]; exact hloc) c hc hγ
    (fun u => transport_budget g hEnorm p hL ha hfit c hc hcLen (γ u) (hγcore u))
  rw [pull_metric_eq g hEnorm p hloc]
  dsimp only at hcont hlen ⊢
  have heq : (fun u => CheegerGromovTaylor.loopTransport g hEnorm p hL ha hfit hloc
      c hc hcLen (γ u) (hγcore u)) =
      fun u => NormalCoordinates.loopTransport g p (complete_domain g hEnorm p R)
        (by rw [framed_exp_eq g hEnorm p]; exact hloc) c hc (γ u)
        (transport_budget g hEnorm p hL ha hfit c hc hcLen (γ u) (hγcore u)) := by
    funext u
    exact transport_eq g hEnorm p hL ha hfit hloc c hc hcLen (γ u) (hγcore u)
  rw [heq]
  exact ⟨hcont, hlen⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_curve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_curve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_curve ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_curve

theorem loopTransport_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    {γ : Real → intrinsicPullBall (E := E) R} {s t : Real}
    (hγ :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ (Set.Icc s t))
    (hγcore : ∀ u : Real, γ u ∈ intrinsicCore (E := E) R a) :
    letI : _root_.Bundle.RiemannianBundle
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨(intrinsicPullMetric (I := I) g hEnorm p hloc).toRiemannianMetric⟩
    Manifold.pathELength 𝓘(Real, E)
        (fun u =>
          loopTransport (I := I) g hEnorm p hL ha hfit hloc
            c hc hcLen (γ u) (hγcore u)) s t =
      Manifold.pathELength 𝓘(Real, E) γ s t :=
  (loopTransport_curve (I := I) g hEnorm p hL ha hfit hloc
    c hc hcLen hγ hγcore).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_len then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_len"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_len ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_len

private theorem transport_edist_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    {x y : intrinsicPullBall (E := E) R}
    (hx : x ∈ intrinsicCore (E := E) R a)
    (hy : y ∈ intrinsicCore (E := E) R a) :
    riemannianEDistOf (intrinsicPullMetric g hEnorm p hloc)
      (loopTransport g hEnorm p hL ha hfit hloc c hc hcLen x hx)
      (loopTransport g hEnorm p hL ha hfit hloc c hc hcLen y hy) ≤
      riemannianEDistOf (intrinsicPullMetric g hEnorm p hloc) x y := by
  classical
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let : _root_.Bundle.RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  obtain ⟨join, hjoin, _⟩ :=
    intrinsicCore_jensen_min (I := I) g hEnorm p hR h4aR hloc
      hK hsmall hRm
  have hspec := hjoin x hx y hy
  let γp : Path x y := {
    toFun := fun t => join x y t
    continuous_toFun := hspec.1.continuous.comp continuous_subtype_val
    source' := hspec.2.2.1
    target' := hspec.2.2.2.1 }
  let γ : Real → intrinsicPullBall (E := E) R := γp.extend
  have hγC1 :
      ContMDiffOn 𝓘(Real, Real) 𝓘(Real, E) 1 γ
        (Set.Icc (0 : Real) 1) := by
    refine (hspec.1.of_le (by decide)).contMDiffOn.congr ?_
    intro t ht
    with_unfolding_all exact γp.extend_apply ht
  have hγcore :
      ∀ t : Real, γ t ∈ intrinsicCore (E := E) R a := by
    intro t
    have htRange : γp.extend t ∈ Set.range γp.extend := ⟨t, rfl⟩
    rw [γp.extend_range] at htRange
    obtain ⟨u, hu⟩ := htRange
    change γp.extend t ∈ intrinsicCore (E := E) R a
    rw [← hu]
    exact hspec.2.2.2.2.2.2 u u.property
  have hjlen : γp.riemannianELength (I := 𝓘(Real, E)) =
      riemannianEDistOf gPull x y := by
    calc
      γp.riemannianELength (I := 𝓘(Real, E)) =
          Manifold.pathELength 𝓘(Real, E) (join x y) 0 1 := by
        apply Manifold.pathELength_congr
        intro t ht
        exact γp.extend_apply ht
      _ = riemannianEDistOf gPull x y :=
        coreJoin_len g hEnorm p hR h4aR hloc hjoin hx hy
  change riemannianEDistOf (intrinsicPullMetric g hEnorm p hloc)
    (loopTransport g hEnorm p hL ha hfit hloc c hc hcLen x hx)
    (loopTransport g hEnorm p hL ha hfit hloc c hc hcLen y hy) ≤
    riemannianEDistOf (intrinsicPullMetric g hEnorm p hloc) x y
  rw [transport_eq g hEnorm p hL ha hfit hloc c hc hcLen x hx,
    transport_eq g hEnorm p hL ha hfit hloc c hc hcLen y hy,
    pull_metric_eq g hEnorm p hloc]
  refine NormalCoordinates.riemannianEDistOf_loopTransport_le_of_path g p
    (complete_domain g hEnorm p R) (by rw [framed_exp_eq g hEnorm p]; exact hloc) c hc
    γp ?_ (fun t => transport_budget g hEnorm p hL ha hfit c hc hcLen (γ t) (hγcore t)) ?_
  · exact hγC1
  · have h := congrArg (fun gm : SmoothRiemannianMetric 𝓘(Real, E)
        (intrinsicPullBall (E := E) R) =>
        let : _root_.Bundle.RiemannianBundle (TangentSpace 𝓘(Real, E) :
            intrinsicPullBall (E := E) R → Type _) := ⟨gm.toRiemannianMetric⟩
        γp.riemannianELength (I := 𝓘(Real, E)) = riemannianEDistOf gm x y)
      (pull_metric_eq g hEnorm p hloc)
    exact h.mp hjlen

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.transport_edist_le
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.transport_edist_le target :: scope.openDecls } }

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
theorem loopTransport_nonexp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    {x y : intrinsicPullBall (E := E) R}
    (hx : x ∈ intrinsicCore (E := E) R a)
    (hy : y ∈ intrinsicCore (E := E) R a) :
    let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
    letI : _root_.Bundle.RiemannianBundle
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
    letI : ConnectedSpace (intrinsicPullBall (E := E) R) :=
      Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
    letI : MetricSpace (intrinsicPullBall (E := E) R) :=
      HopfRinow.riemMetricSpace
        (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
    _root_.Dist.dist
        (loopTransport (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen x hx)
        (loopTransport (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen y hy) ≤
      dist x y := by
  classical
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let : _root_.Bundle.RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  let : ConnectedSpace (intrinsicPullBall (E := E) R) :=
    Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
  let : MetricSpace (intrinsicPullBall (E := E) R) :=
    HopfRinow.riemMetricSpace
      (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
  have hed := transport_edist_le g hEnorm p hR h4aR hL ha hfit hloc
    hK hsmall hRm c hc hcLen hx hy
  have hedReal :
      (_root_.Manifold.riemannianEDist 𝓘(Real, E)
        (loopTransport (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen x hx)
        (loopTransport (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen y hy)).toReal ≤
      (_root_.Manifold.riemannianEDist 𝓘(Real, E) x y).toReal :=
    ENNReal.toReal_mono
      (riemannianEDist_ne_top (I := 𝓘(Real, E)) x y) hed
  calc
    _root_.Dist.dist
          (loopTransport (I := I) g hEnorm p hL ha hfit hloc
            c hc hcLen x hx)
          (loopTransport (I := I) g hEnorm p hL ha hfit hloc
            c hc hcLen y hy) =
        (_root_.Manifold.riemannianEDist 𝓘(Real, E)
          (loopTransport (I := I) g hEnorm p hL ha hfit hloc
            c hc hcLen x hx)
          (loopTransport (I := I) g hEnorm p hL ha hfit hloc
            c hc hcLen y hy)).toReal :=
      HopfRinow.riemMetric_dist_eq
        (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R) _ _
    _ ≤ (_root_.Manifold.riemannianEDist 𝓘(Real, E) x y).toReal := hedReal
    _ = _root_.Dist.dist x y :=
      (HopfRinow.riemMetric_dist_eq
        (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R) x y).symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_nonexp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_nonexp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_nonexp ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_nonexp

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
theorem loopIter_nonexp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (n : Nat) {x y : intrinsicPullBall (E := E) R}
    (hx :
      ∀ k < n,
        ((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen)^[k]) x ∈ intrinsicCore (E := E) R a)
    (hy :
      ∀ k < n,
        ((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen)^[k]) y ∈ intrinsicCore (E := E) R a) :
    let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
    letI : _root_.Bundle.RiemannianBundle
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
    letI : ConnectedSpace (intrinsicPullBall (E := E) R) :=
      Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
    letI : MetricSpace (intrinsicPullBall (E := E) R) :=
      HopfRinow.riemMetricSpace
        (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
    _root_.Dist.dist
        (((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen)^[n]) x)
        (((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen)^[n]) y) ≤
      dist x y := by
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let : _root_.Bundle.RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  let : ConnectedSpace (intrinsicPullBall (E := E) R) :=
    Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
  let : MetricSpace (intrinsicPullBall (E := E) R) :=
    HopfRinow.riemMetricSpace
      (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
  let T : intrinsicPullBall (E := E) R → intrinsicPullBall (E := E) R :=
    loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen
  change _root_.Dist.dist ((T^[n]) x) ((T^[n]) y) ≤ _root_.Dist.dist x y
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hxn : (T^[n]) x ∈ intrinsicCore (E := E) R a :=
        hx n (Nat.lt_succ_self n)
      have hyn : (T^[n]) y ∈ intrinsicCore (E := E) R a :=
        hy n (Nat.lt_succ_self n)
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      calc
        _root_.Dist.dist (T ((T^[n]) x)) (T ((T^[n]) y)) =
            _root_.Dist.dist
              (loopTransport (I := I) g hEnorm p hL ha hfit hloc
                c hc hcLen ((T^[n]) x) hxn)
              (loopTransport (I := I) g hEnorm p hL ha hfit hloc
                c hc hcLen ((T^[n]) y) hyn) := by
                  exact congrArg₂ _root_.Dist.dist
                    (loopTransportExt_eq (I := I) g hEnorm p
                      hL ha hfit hloc c hc hcLen ((T^[n]) x) hxn)
                    (loopTransportExt_eq (I := I) g hEnorm p
                      hL ha hfit hloc c hc hcLen ((T^[n]) y) hyn)
        _ ≤ _root_.Dist.dist ((T^[n]) x) ((T^[n]) y) :=
          loopTransport_nonexp (I := I) g hEnorm p hR h4aR
            hL ha hfit hloc hK hsmall hRm c hc hcLen hxn hyn
        _ ≤ _root_.Dist.dist x y :=
          ih (fun k hk => hx k (hk.trans (Nat.lt_succ_self n)))
            (fun k hk => hy k (hk.trans (Nat.lt_succ_self n)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopIter_nonexp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopIter_nonexp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopIter_nonexp ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopIter_nonexp

theorem loopTransport_ne
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a : Real} (hL : 0 ≤ L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (A : IntrinsicFrameLift (I := I) g hEnorm p c.extend 0 1)
    (hA : A.toFun 1 ≠ 0)
    (z : intrinsicPullBall (E := E) R)
    (hz : z ∈ intrinsicCore (E := E) R a) :
    loopTransport (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen z hz ≠ z := by
  rw [transport_eq g hEnorm p hL ha hfit hloc c hc hcLen z hz]
  have hR : 0 < R := (add_nonneg hL ha).trans_lt hfit
  have hcR : c.riemannianELength (I := I) < ENNReal.ofReal R :=
    hcLen.trans ((ENNReal.ofReal_lt_ofReal_iff hR).mpr (by linarith))
  apply NormalCoordinates.loopTransport_ne_of_lift_end_ne
  · rw [framed_exp_eq g hEnorm p]
    exact ⟨A.contDiff.continuousOn, A.start,
      fun t ht => ⟨A.maps_ball hR hcR ht, A.lifts ht⟩⟩
  · exact hA

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_ne ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.loopTransport_ne

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
theorem intrinsicCore_center
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a r K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (points : ι → intrinsicPullBall (E := E) R)
    (hr : 0 < r) (h2ra : 2 * r < a)
    (hpts : ∀ i : ι, ‖(points i : E)‖ < r) :
    let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
    letI : _root_.Bundle.RiemannianBundle
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
    letI : ConnectedSpace (intrinsicPullBall (E := E) R) :=
      Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
    letI : MetricSpace (intrinsicPullBall (E := E) R) :=
      HopfRinow.riemMetricSpace
        (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
    ∃ c ∈ intrinsicCore (E := E) R a,
      (∀ z : intrinsicPullBall (E := E) R,
        CenterOfMass.metricEnergy (fun _ : ι => (1 : Real)) points c ≤
          CenterOfMass.metricEnergy (fun _ : ι => (1 : Real)) points z) ∧
      ∀ y : intrinsicPullBall (E := E) R,
        (∀ z : intrinsicPullBall (E := E) R,
          CenterOfMass.metricEnergy (fun _ : ι => (1 : Real)) points y ≤
            CenterOfMass.metricEnergy (fun _ : ι => (1 : Real)) points z) →
        y = c := by
  classical
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let : _root_.Bundle.RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  let : ConnectedSpace (intrinsicPullBall (E := E) R) :=
    Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
  let : MetricSpace (intrinsicPullBall (E := E) R) :=
    HopfRinow.riemMetricSpace
      (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
  let z₀ := intrinsicZero (E := E) hR
  have ha : 0 < a := by linarith
  have haR : a < R := by linarith
  have hra : r < a := by linarith
  have hzeroDist :
      ∀ q : intrinsicPullBall (E := E) R, _root_.Dist.dist z₀ q = ‖(q : E)‖ := by
    intro q
    calc
      _root_.Dist.dist z₀ q =
          (_root_.Manifold.riemannianEDist 𝓘(Real, E) z₀ q).toReal :=
        HopfRinow.riemMetric_dist_eq
          (I := 𝓘(Real, E))
          (M := intrinsicPullBall (E := E) R) z₀ q
      _ = (riemannianEDistOf
          (I := 𝓘(Real, E)) gPull z₀ q).toReal := rfl
      _ = (ENNReal.ofReal ‖(q : E)‖).toReal := by
        rw [intrinsicPull_dist_zero (I := I) g hEnorm p hR hloc q]
      _ = ‖(q : E)‖ := ENNReal.toReal_ofReal (norm_nonneg _)
  have hptsCore : ∀ i : ι, points i ∈ intrinsicCore (E := E) R a := by
    intro i
    exact (hpts i).le.trans hra.le
  obtain ⟨join, hjensen⟩ :=
    intrinsicCore_jensen (I := I) g hEnorm p hR h4aR hloc hK hsmall hRm
  have hfar :
      ∀ q : intrinsicPullBall (E := E) R,
        q ∉ intrinsicCore (E := E) R a → 2 * r ≤ _root_.Dist.dist z₀ q := by
    intro q hq
    have haq : a < ‖(q : E)‖ := by
      rw [mem_intrCore] at hq
      exact lt_of_not_ge hq
    rw [hzeroDist q]
    linarith
  let i₀ : ι := Classical.choice inferInstance
  exact CenterOfMass.exists_unique_global
    (fun _ : ι => (1 : Real)) points
    (intrinsicCore_compact (E := E) haR)
    (intrinsicZero_mem (E := E) hR ha.le) hr
    (fun i => by
      rw [hzeroDist (points i)]
      exact hpts i)
    hfar (fun _ => by norm_num) ⟨i₀, by norm_num⟩
    (fun i => hjensen (points i) (hptsCore i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCore_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCore_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCore_center ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCore_center

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
theorem intrinsicCycle_center
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 < L)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    {n : Nat} [NeZero n]
    (points : Fin n → intrinsicPullBall (E := E) R)
    (hptsCore : ∀ i, points i ∈ intrinsicCore (E := E) R a) :
    let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
    letI : _root_.Bundle.RiemannianBundle
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
    letI : ConnectedSpace (intrinsicPullBall (E := E) R) :=
      Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
    letI : MetricSpace (intrinsicPullBall (E := E) R) :=
      HopfRinow.riemMetricSpace
        (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
    ∀ (_ :
        ∀ i, _root_.Dist.dist (points 0) (points i) ≤ (i.val : Real) * L)
      (_ :
        ∀ q : intrinsicPullBall (E := E) R,
          q ∉ intrinsicCore (E := E) R a →
            (n : Real) * L < _root_.Dist.dist (points 0) q),
      ∃ c ∈ intrinsicCore (E := E) R a,
      (∀ z : intrinsicPullBall (E := E) R,
        CenterOfMass.metricEnergy (fun _ : Fin n => (1 : Real)) points c ≤
          CenterOfMass.metricEnergy (fun _ : Fin n => (1 : Real)) points z) ∧
      ∀ y : intrinsicPullBall (E := E) R,
        (∀ z : intrinsicPullBall (E := E) R,
          CenterOfMass.metricEnergy (fun _ : Fin n => (1 : Real)) points y ≤
            CenterOfMass.metricEnergy (fun _ : Fin n => (1 : Real)) points z) →
        y = c := by
  classical
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let : _root_.Bundle.RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  let : ConnectedSpace (intrinsicPullBall (E := E) R) :=
    Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
  let : MetricSpace (intrinsicPullBall (E := E) R) :=
    HopfRinow.riemMetricSpace
      (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
  dsimp only
  intro hgraded hfar
  have haR : a < R := by
    linarith
  obtain ⟨join, hjensen⟩ :=
    intrinsicCore_jensen (I := I) g hEnorm p hR h4aR hloc hK hsmall hRm
  have henergy :
      ∀ q : intrinsicPullBall (E := E) R,
        q ∉ intrinsicCore (E := E) R a →
          CenterOfMass.metricEnergy
              (fun _ : Fin n => (1 : Real)) points (points 0) <
            CenterOfMass.metricEnergy
              (fun _ : Fin n => (1 : Real)) points q := by
    intro q hq
    have hterm :
        ∀ i : Fin n,
          _root_.Dist.dist (points 0) (points i) ^ 2 <
            dist q (points i.rev) ^ 2 := by
      intro i
      have hval :
          i.val + i.rev.val + 1 = n := by
        simp only [Fin.rev, Fin.val_mk]
        omega
      have hpair :
          (i.val : Real) * L + (i.rev.val : Real) * L <
            (n : Real) * L := by
        have hvalReal :
            (i.val : Real) + (i.rev.val : Real) + 1 = (n : Real) := by
          exact_mod_cast hval
        nlinarith
      have htri :
          _root_.Dist.dist (points 0) q ≤
            dist (points 0) (points i.rev) + _root_.Dist.dist (points i.rev) q :=
        dist_triangle _ _ _
      have hdist :
          dist (points 0) (points i) < _root_.Dist.dist q (points i.rev) := by
        have hqfar := hfar q hq
        have hi := hgraded i
        have hirev := hgraded i.rev
        rw [dist_comm (points i.rev) q] at htri
        have hsum :
            (i.val : Real) * L + (i.rev.val : Real) * L <
              dist (points 0) (points i.rev) + _root_.Dist.dist q (points i.rev) :=
          (hpair.trans hqfar).trans_le htri
        have hiright :
            (i.val : Real) * L < _root_.Dist.dist q (points i.rev) := by
          linarith
        exact hi.trans_lt hiright
      exact (sq_lt_sq₀ dist_nonneg dist_nonneg).mpr hdist
    have hsum :
        (∑ i : Fin n, _root_.Dist.dist (points 0) (points i) ^ 2) <
          ∑ i : Fin n, _root_.Dist.dist q (points i.rev) ^ 2 := by
      apply Finset.sum_lt_sum
      · intro i _
        exact (hterm i).le
      · exact ⟨0, Finset.mem_univ _, hterm 0⟩
    have hrev :
        (∑ i : Fin n, _root_.Dist.dist q (points i.rev) ^ 2) =
          ∑ i : Fin n, _root_.Dist.dist q (points i) ^ 2 := by
      simpa only [Fin.revPerm_apply] using
        (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin n))
          (fun i : Fin n => _root_.Dist.dist q (points i) ^ 2))
    unfold CenterOfMass.metricEnergy
    apply mul_lt_mul_of_pos_left _ (by norm_num)
    simpa only [one_mul] using hsum.trans_eq hrev
  exact CenterOfMass.exists_global_of_lt
    (fun _ : Fin n => (1 : Real)) points
    (intrinsicCore_compact (E := E) haR) (hptsCore 0)
    henergy (fun _ => by norm_num) ⟨0, by norm_num⟩
    (fun i => hjensen (points i) (hptsCore i))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCycle_center then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCycle_center"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCycle_center ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCycle_center

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
theorem intrinsicCycle_not_fin
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (hLpos : 0 < L) (ha : 0 ≤ a)
    (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (A : IntrinsicFrameLift (I := I) g hEnorm p c.extend 0 1)
    (hA : A.toFun 1 ≠ 0)
    {n : Nat} [NeZero n]
    (points : Fin n → intrinsicPullBall (E := E) R)
    (hptsCore : ∀ i, points i ∈ intrinsicCore (E := E) R a) :
    let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
    letI : _root_.Bundle.RiemannianBundle
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
    letI : ConnectedSpace (intrinsicPullBall (E := E) R) :=
      Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
    letI : MetricSpace (intrinsicPullBall (E := E) R) :=
      HopfRinow.riemMetricSpace
        (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
    ∀ (_ :
        ∀ i, _root_.Dist.dist (points 0) (points i) ≤ (i.val : Real) * L)
      (_ :
        ∀ q : intrinsicPullBall (E := E) R,
          q ∉ intrinsicCore (E := E) R a →
            (n : Real) * L < _root_.Dist.dist (points 0) q)
      (e : Equiv.Perm (Fin n)),
      ¬ ∀ i : Fin n,
        loopTransport (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen (points i) (hptsCore i) = points (e i) := by
  classical
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let : _root_.Bundle.RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  let : ConnectedSpace (intrinsicPullBall (E := E) R) :=
    Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
  let : MetricSpace (intrinsicPullBall (E := E) R) :=
    HopfRinow.riemMetricSpace
      (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
  dsimp only
  intro hgraded hfar e hperm
  obtain ⟨z, hz, hzmin, hzuniq⟩ :=
    intrinsicCycle_center (I := I) g hEnorm p hR h4aR hLpos
      hloc hK hsmall hRm points hptsCore hgraded hfar
  let T : intrinsicPullBall (E := E) R → intrinsicPullBall (E := E) R :=
    fun q =>
      if hq : q ∈ intrinsicCore (E := E) R a then
        loopTransport (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen q hq
      else q
  have hTpts : ∀ i : Fin n, T (points i) = points (e i) := by
    intro i
    simp only [T, dif_pos (hptsCore i)]
    exact hperm i
  have hTdist :
      ∀ i : Fin n, _root_.Dist.dist (T z) (T (points i)) ≤ _root_.Dist.dist z (points i) := by
    intro i
    simp only [T, dif_pos hz, dif_pos (hptsCore i)]
    exact
      loopTransport_nonexp (I := I) g hEnorm p hR h4aR
        hL ha hfit hloc hK hsmall hRm c hc hcLen hz (hptsCore i)
  have hfixT : T z = z :=
    CenterOfMass.fixed_of_nonexp
      (fun _ : Fin n => (1 : Real)) points T e z hzmin hzuniq
      (fun _ => by norm_num) (fun _ => rfl) hTpts hTdist
  have hfix :
      loopTransport (I := I) g hEnorm p hL ha hfit hloc
        c hc hcLen z hz = z := by
    simpa only [T, dif_pos hz] using hfixT
  exact
    (loopTransport_ne (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen A hA z hz) hfix

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCycle_not_fin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCycle_not_fin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCycle_not_fin ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCycle_not_fin

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
theorem intrinsicOrbit_not_finite
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a r K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (A : IntrinsicFrameLift (I := I) g hEnorm p c.extend 0 1)
    (hA : A.toFun 1 ≠ 0)
    {ι : Type*} [Finite ι] [Nonempty ι]
    (points : ι → intrinsicPullBall (E := E) R)
    (hr : 0 < r) (h2ra : 2 * r < a)
    (hpts : ∀ i : ι, ‖(points i : E)‖ < r)
    (e : ι ≃ ι) :
    let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
    letI : _root_.Bundle.RiemannianBundle
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
    letI : ConnectedSpace (intrinsicPullBall (E := E) R) :=
      Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
    letI : MetricSpace (intrinsicPullBall (E := E) R) :=
      HopfRinow.riemMetricSpace
        (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
    ¬ ∀ i : ι, ∀ hi : points i ∈ intrinsicCore (E := E) R a,
      loopTransport (I := I) g hEnorm p hL ha hfit hloc
        c hc hcLen (points i) hi = points (e i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let : _root_.Bundle.RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  let : ConnectedSpace (intrinsicPullBall (E := E) R) :=
    Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
  let : MetricSpace (intrinsicPullBall (E := E) R) :=
    HopfRinow.riemMetricSpace
      (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
  change
    ¬ ∀ i : ι, ∀ hi : points i ∈ intrinsicCore (E := E) R a,
      loopTransport (I := I) g hEnorm p hL ha hfit hloc
        c hc hcLen (points i) hi = points (e i)
  intro hperm
  have hra : r < a := by linarith
  have hptsCore :
      ∀ i : ι, points i ∈ intrinsicCore (E := E) R a := by
    intro i
    exact (hpts i).le.trans hra.le
  obtain ⟨z, hz, hzmin, hzuniq⟩ :=
    intrinsicCore_center (I := I) g hEnorm p hR h4aR hloc
      hK hsmall hRm points hr h2ra hpts
  let T : intrinsicPullBall (E := E) R → intrinsicPullBall (E := E) R :=
    fun q =>
      if hq : q ∈ intrinsicCore (E := E) R a then
        loopTransport (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen q hq
      else q
  have hTpts :
      ∀ i : ι, T (points i) = points (e i) := by
    intro i
    simp only [T, dif_pos (hptsCore i)]
    exact hperm i (hptsCore i)
  have hTdist :
      ∀ i : ι, _root_.Dist.dist (T z) (T (points i)) ≤ _root_.Dist.dist z (points i) := by
    intro i
    simp only [T, dif_pos hz, dif_pos (hptsCore i)]
    exact
      loopTransport_nonexp (I := I) g hEnorm p hR h4aR
        hL ha hfit hloc hK hsmall hRm c hc hcLen hz (hptsCore i)
  have hfixT : T z = z :=
    CenterOfMass.fixed_of_nonexp
      (fun _ : ι => (1 : Real)) points T e z hzmin hzuniq
      (fun _ => by norm_num) (fun _ => rfl) hTpts hTdist
  have hfix :
      loopTransport (I := I) g hEnorm p hL ha hfit hloc
        c hc hcLen z hz = z := by
    simpa only [T, dif_pos hz] using hfixT
  exact
    (loopTransport_ne (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen A hA z hz) hfix

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicOrbit_not_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicOrbit_not_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicOrbit_not_finite ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicOrbit_not_finite

theorem intrinsicIter_ne
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a r K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (A : IntrinsicFrameLift (I := I) g hEnorm p c.extend 0 1)
    (hA : A.toFun 1 ≠ 0)
    {n : Nat} [NeZero n]
    (hr : 0 < r) (h2ra : 2 * r < a)
    (q : intrinsicPullBall (E := E) R)
    (hiter :
      ∀ j < n,
        ‖(((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen)^[j]) q : E)‖ < r) :
    ((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen)^[n]) q ≠ q := by
  classical
  let T : intrinsicPullBall (E := E) R → intrinsicPullBall (E := E) R :=
    loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen
  change (T^[n]) q ≠ q
  intro hperiod
  let points : ZMod n → intrinsicPullBall (E := E) R :=
    fun i => (T^[i.val]) q
  have hpts :
      ∀ i : ZMod n, ‖(points i : E)‖ < r := by
    intro i
    exact hiter i.val (ZMod.val_lt i)
  have hnot :
      ¬ ∀ i : ZMod n,
        ∀ hi : points i ∈ intrinsicCore (E := E) R a,
          loopTransport (I := I) g hEnorm p hL ha hfit hloc
            c hc hcLen (points i) hi =
              points ((Equiv.addRight (1 : ZMod n)) i) := by
    simpa only using
      (intrinsicOrbit_not_finite (I := I) g hEnorm p hR h4aR
        hL ha hfit hloc hK hsmall hRm c hc hcLen A hA
        points hr h2ra hpts (Equiv.addRight (1 : ZMod n)))
  apply hnot
  intro i hi
  rw [← loopTransportExt_eq (I := I) g hEnorm p hL ha hfit hloc
    c hc hcLen (points i) hi]
  change T ((T^[i.val]) q) =
    (T^[((Equiv.addRight (1 : ZMod n)) i).val]) q
  rw [← Function.iterate_succ_apply' T i.val q]
  have hval :
      ((Equiv.addRight (1 : ZMod n)) i).val =
        (i.val + 1) % n := by
    change (i + 1).val = (i.val + 1) % n
    rw [ZMod.val_add]
    have hone : ZMod.val (1 : ZMod n) = 1 % n := by
      simpa using ZMod.val_natCast n 1
    rw [hone]
    by_cases hn1 : n = 1
    · subst n
      norm_num
    · have h1n : 1 < n := by
        have hnPos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
        omega
      rw [Nat.mod_eq_of_lt h1n]
  rw [hval]
  by_cases hiNext : i.val + 1 < n
  · rw [Nat.mod_eq_of_lt hiNext]
  · have hiEq : i.val + 1 = n := by
      have hiLt := ZMod.val_lt i
      omega
    have hmod : (i.val + 1) % n = 0 := by
      rw [hiEq, Nat.mod_self]
    rw [hmod, Function.iterate_zero_apply]
    have hiSucc : i.val.succ = n := by
      omega
    rw [hiSucc, hperiod]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_ne then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_ne"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_ne ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_ne

theorem intrinsicIter_ne_of_lt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a r K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (A : IntrinsicFrameLift (I := I) g hEnorm p c.extend 0 1)
    (hA : A.toFun 1 ≠ 0)
    {i j : Nat} (hij : i < j)
    (hr : 0 < r) (h2ra : 2 * r < a)
    (q : intrinsicPullBall (E := E) R)
    (hiter :
      ∀ k < j,
        ‖(((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen)^[k]) q : E)‖ < r) :
    ((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen)^[i]) q ≠
      ((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
        c hc hcLen)^[j]) q := by
  let T : intrinsicPullBall (E := E) R → intrinsicPullBall (E := E) R :=
    loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen
  change (T^[i]) q ≠ (T^[j]) q
  intro heq
  have hnPos : 0 < j - i := Nat.sub_pos_of_lt hij
  let : NeZero (j - i) := ⟨Nat.ne_of_gt hnPos⟩
  have hsub :
      ∀ m < j - i,
        ‖((T^[m]) ((T^[i]) q) : E)‖ < r := by
    intro m hm
    rw [← Function.iterate_add_apply]
    have hmj : m + i < j := by
      omega
    exact hiter (m + i) hmj
  have hcycle :
      (T^[j - i]) ((T^[i]) q) = (T^[i]) q := by
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij.le]
    exact heq.symm
  exact
    (intrinsicIter_ne (I := I) g hEnorm p hR h4aR hL ha hfit hloc
      hK hsmall hRm c hc hcLen A hA (n := j - i)
      hr h2ra ((T^[i]) q) hsub) hcycle

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_ne_of_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_ne_of_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_ne_of_lt ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_ne_of_lt

theorem intrinsicIter_injective
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a r K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (A : IntrinsicFrameLift (I := I) g hEnorm p c.extend 0 1)
    (hA : A.toFun 1 ≠ 0)
    (N : Nat) (hr : 0 < r) (h2ra : 2 * r < a)
    (hNL : (N : Real) * L < r) :
    Function.Injective
      (fun i : Fin (N + 1) =>
        ((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen)^[i.val]) (intrinsicZero (E := E) hR)) := by
  have hra : r < a := by
    linarith
  have hbound :
      ∀ k ≤ N,
        ‖(((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen)^[k]) (intrinsicZero (E := E) hR) : E)‖ < r := by
    intro k hk
    have hkCast : (k : Real) ≤ (N : Real) := by
      exact_mod_cast hk
    have hkMul : (k : Real) * L ≤ (N : Real) * L :=
      mul_le_mul_of_nonneg_right hkCast hL
    have hka : (k : Real) * L < a :=
      (hkMul.trans_lt hNL).trans hra
    exact
      (intrinsicIter_norm (I := I) g hEnorm p hR hL ha hfit hloc
        c hc hcLen k hka).trans_lt (hkMul.trans_lt hNL)
  intro i j heq
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hij | hji
  · exact
      (intrinsicIter_ne_of_lt (I := I) g hEnorm p hR h4aR
        hL ha hfit hloc hK hsmall hRm c hc hcLen A hA
        hij hr h2ra (intrinsicZero (E := E) hR)
        (fun k hk =>
          hbound k
            (hk.le.trans (Nat.lt_succ_iff.mp j.isLt)))) heq
  · exact
      (intrinsicIter_ne_of_lt (I := I) g hEnorm p hR h4aR
        hL ha hfit hloc hK hsmall hRm c hc hcLen A hA
        hji hr h2ra (intrinsicZero (E := E) hR)
        (fun k hk =>
          hbound k
            (hk.le.trans (Nat.lt_succ_iff.mp i.isLt)))) heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_injective ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_injective

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
theorem intrinsicIter_injective_of_nonzero_frameLift
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (A : IntrinsicFrameLift (I := I) g hEnorm p c.extend 0 1)
    (hA : A.toFun 1 ≠ 0)
    (N : Nat) (hNLa : (N : Real) * L < a) :
    Function.Injective
      (fun i : Fin (N + 1) =>
        ((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen)^[i.val]) (intrinsicZero (E := E) hR)) := by
  classical
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let : _root_.Bundle.RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  let : ConnectedSpace (intrinsicPullBall (E := E) R) :=
    Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
  let : MetricSpace (intrinsicPullBall (E := E) R) :=
    HopfRinow.riemMetricSpace
      (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
  let z₀ := intrinsicZero (E := E) hR
  let T : intrinsicPullBall (E := E) R → intrinsicPullBall (E := E) R :=
    loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen
  have hLpos : 0 < L := by
    exact ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hcLen)
  have hzeroDist :
      ∀ q : intrinsicPullBall (E := E) R, _root_.Dist.dist z₀ q = ‖(q : E)‖ := by
    intro q
    calc
      _root_.Dist.dist z₀ q =
          (_root_.Manifold.riemannianEDist 𝓘(Real, E) z₀ q).toReal :=
        HopfRinow.riemMetric_dist_eq
          (I := 𝓘(Real, E))
          (M := intrinsicPullBall (E := E) R) z₀ q
      _ = (riemannianEDistOf
          (I := 𝓘(Real, E)) gPull z₀ q).toReal := rfl
      _ = (ENNReal.ofReal ‖(q : E)‖).toReal := by
        rw [intrinsicPull_dist_zero (I := I) g hEnorm p hR hloc q]
      _ = ‖(q : E)‖ := ENNReal.toReal_ofReal (norm_nonneg _)
  have hbound :
      ∀ k ≤ N, ‖((T^[k]) z₀ : E)‖ ≤ (k : Real) * L := by
    intro k hk
    have hkCast : (k : Real) ≤ (N : Real) := by
      exact_mod_cast hk
    have hkMul : (k : Real) * L ≤ (N : Real) * L :=
      mul_le_mul_of_nonneg_right hkCast hL
    exact
      intrinsicIter_norm (I := I) g hEnorm p hR hL ha hfit hloc
        c hc hcLen k (hkMul.trans_lt hNLa)
  have hcore :
      ∀ k ≤ N, (T^[k]) z₀ ∈ intrinsicCore (E := E) R a := by
    intro k hk
    rw [mem_intrCore]
    exact (hbound k hk).trans (by
      have hkCast : (k : Real) ≤ (N : Real) := by
        exact_mod_cast hk
      exact
        (mul_le_mul_of_nonneg_right hkCast hL).trans
          (hNLa.le))
  have hdistinct :
      ∀ {i j : Nat}, i < j → j ≤ N → (T^[i]) z₀ ≠ (T^[j]) z₀ := by
    intro i j hij hjN heq
    let n : Nat := j - i
    have hnPos : 0 < n := by
      dsimp only [n]
      exact Nat.sub_pos_of_lt hij
    let : NeZero n := ⟨Nat.ne_of_gt hnPos⟩
    let points : Fin n → intrinsicPullBall (E := E) R :=
      fun k => (T^[i + k.val]) z₀
    have hptsCore :
        ∀ k : Fin n, points k ∈ intrinsicCore (E := E) R a := by
      intro k
      have hikj : i + k.val < j := by
        dsimp only [n] at k
        omega
      exact hcore (i + k.val) (hikj.le.trans hjN)
    have hgraded :
        ∀ k : Fin n,
          dist (points 0) (points k) ≤ (k.val : Real) * L := by
      intro k
      have hiN : i ≤ N := hij.le.trans hjN
      have hkN : k.val ≤ N := by
        have hikj : i + k.val < j := by
          dsimp only [n] at k
          omega
        omega
      have hxCore :
          ∀ m < i, (T^[m]) z₀ ∈ intrinsicCore (E := E) R a := by
        intro m hm
        exact hcore m (hm.le.trans hiN)
      have hyCore :
          ∀ m < i,
            (T^[m]) ((T^[k.val]) z₀) ∈
              intrinsicCore (E := E) R a := by
        intro m hm
        rw [← Function.iterate_add_apply]
        have hmkj : m + k.val < j := by
          have hklt : k.val < n := k.isLt
          dsimp only [n] at hklt
          omega
        exact hcore (m + k.val) (hmkj.le.trans hjN)
      have hnonexp :
          _root_.Dist.dist ((T^[i]) z₀) ((T^[i]) ((T^[k.val]) z₀)) ≤
            dist z₀ ((T^[k.val]) z₀) := by
        simpa only [T] using
          (loopIter_nonexp (I := I) g hEnorm p hR h4aR
            hL ha hfit hloc hK hsmall hRm c hc hcLen i
            hxCore hyCore)
      change
        _root_.Dist.dist ((T^[i + 0]) z₀) ((T^[i + k.val]) z₀) ≤
          (k.val : Real) * L
      rw [Nat.add_zero, Function.iterate_add_apply]
      exact hnonexp.trans ((hzeroDist _).trans_le (hbound k.val hkN))
    have hfar :
        ∀ q : intrinsicPullBall (E := E) R,
          q ∉ intrinsicCore (E := E) R a →
            (n : Real) * L < _root_.Dist.dist (points 0) q := by
      intro q hq
      have haq : a < ‖(q : E)‖ := by
        rw [mem_intrCore] at hq
        exact lt_of_not_ge hq
      have hiN : i ≤ N := hij.le.trans hjN
      have hiDist :
          dist z₀ (points 0) ≤ (i : Real) * L := by
        change _root_.Dist.dist z₀ ((T^[i + 0]) z₀) ≤ (i : Real) * L
        rw [Nat.add_zero, hzeroDist]
        exact hbound i hiN
      have hjCast : (j : Real) ≤ (N : Real) := by
        exact_mod_cast hjN
      have hjMul : (j : Real) * L ≤ (N : Real) * L :=
        mul_le_mul_of_nonneg_right hjCast hL
      have hnAdd : n + i = j := by
        dsimp only [n]
        omega
      have hnAddReal : (n : Real) + (i : Real) = (j : Real) := by
        exact_mod_cast hnAdd
      have hnMul :
          (n : Real) * L + (i : Real) * L = (j : Real) * L := by
        nlinarith
      have htri :
          dist z₀ q ≤ _root_.Dist.dist z₀ (points 0) + _root_.Dist.dist (points 0) q :=
        dist_triangle _ _ _
      rw [hzeroDist q] at htri
      linarith
    let e : Equiv.Perm (Fin n) := Equiv.addRight (1 : Fin n)
    have hnot :
        ¬ ∀ k : Fin n,
          loopTransport (I := I) g hEnorm p hL ha hfit hloc
            c hc hcLen (points k) (hptsCore k) = points (e k) := by
      simpa only using
        (intrinsicCycle_not_fin (I := I) g hEnorm p hR h4aR
          hL hLpos ha hfit hloc hK hsmall hRm c hc hcLen A hA
          points hptsCore hgraded hfar e)
    apply hnot
    intro k
    rw [← loopTransportExt_eq (I := I) g hEnorm p hL ha hfit hloc
      c hc hcLen (points k) (hptsCore k)]
    change T ((T^[i + k.val]) z₀) =
      (T^[i + (e k).val]) z₀
    rw [← Function.iterate_succ_apply' T (i + k.val) z₀]
    have hval : (e k).val = (k.val + 1) % n := by
      change ((k + 1 : Fin n).val) = (k.val + 1) % n
      simp only [Fin.val_add, Fin.val_one']
      calc
        (k.val + 1 % n) % n =
            (k.val % n + 1 % n) % n := by
              rw [Nat.mod_eq_of_lt k.isLt]
        _ = (k.val + 1) % n := (Nat.add_mod k.val 1 n).symm
    rw [hval]
    by_cases hkNext : k.val + 1 < n
    · rw [Nat.mod_eq_of_lt hkNext]
      congr 1
    · have hkEq : k.val + 1 = n := by
        omega
      have hmod : (k.val + 1) % n = 0 := by
        rw [hkEq, Nat.mod_self]
      rw [hmod, Nat.add_zero]
      have hlast : (i + k.val).succ = j := by
        omega
      rw [hlast]
      exact heq.symm
  intro i j heq
  apply Fin.ext
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hij | hji
  · exact
      (hdistinct hij (Nat.lt_succ_iff.mp j.isLt)) heq
  · exact
      (hdistinct hji (Nat.lt_succ_iff.mp i.isLt)) heq.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_injective_of_nonzero_frameLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_injective_of_nonzero_frameLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_injective_of_nonzero_frameLift ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_injective_of_nonzero_frameLift

theorem intrinsicIter_family
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a r K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (A : IntrinsicFrameLift (I := I) g hEnorm p c.extend 0 1)
    (hA : A.toFun 1 ≠ 0)
    (N : Nat) (hr : 0 < r) (h2ra : 2 * r < a)
    (hNL : (N : Real) * L < r) :
    let points : Fin (N + 1) → intrinsicPullBall (E := E) R :=
      fun i =>
        ((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen)^[i.val]) (intrinsicZero (E := E) hR)
    Function.Injective points ∧
      (∀ i, intrinsicFramedExp (I := I) g hEnorm p (points i : E) = p) ∧
      ∀ i, ‖(points i : E)‖ ≤ (i.val : Real) * L := by
  dsimp only
  refine ⟨intrinsicIter_injective (I := I) g hEnorm p hR h4aR
    hL ha hfit hloc hK hsmall hRm c hc hcLen A hA N hr h2ra hNL,
    ?_, ?_⟩
  · intro i
    exact intrinsicIter_exp (I := I) g hEnorm p hR hL ha hfit hloc
      c hc hcLen i.val
  · intro i
    have hiN : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
    have hiCast : (i.val : Real) ≤ (N : Real) := by
      exact_mod_cast hiN
    have hiMul : (i.val : Real) * L ≤ (N : Real) * L :=
      mul_le_mul_of_nonneg_right hiCast hL
    have hra : r < a := by
      linarith
    have hia : (i.val : Real) * L < a :=
      (hiMul.trans_lt hNL).trans hra
    exact intrinsicIter_norm (I := I) g hEnorm p hR hL ha hfit hloc
      c hc hcLen i.val hia

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_family then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_family"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_family ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_family

theorem intrinsicIter_family_of_nonzero_frameLift
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (A : IntrinsicFrameLift (I := I) g hEnorm p c.extend 0 1)
    (hA : A.toFun 1 ≠ 0)
    (N : Nat) (hNLa : (N : Real) * L < a) :
    let points : Fin (N + 1) → intrinsicPullBall (E := E) R :=
      fun i =>
        ((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
          c hc hcLen)^[i.val]) (intrinsicZero (E := E) hR)
    Function.Injective points ∧
      (∀ i, intrinsicFramedExp (I := I) g hEnorm p (points i : E) = p) ∧
      ∀ i, ‖(points i : E)‖ ≤ (i.val : Real) * L := by
  dsimp only
  refine ⟨intrinsicIter_injective_of_nonzero_frameLift (I := I) g hEnorm p hR h4aR
    hL ha hfit hloc hK hsmall hRm c hc hcLen A hA N hNLa,
    ?_, ?_⟩
  · intro i
    exact intrinsicIter_exp (I := I) g hEnorm p hR hL ha hfit hloc
      c hc hcLen i.val
  · intro i
    have hiN : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
    have hiCast : (i.val : Real) ≤ (N : Real) := by
      exact_mod_cast hiN
    have hiMul : (i.val : Real) * L ≤ (N : Real) * L :=
      mul_le_mul_of_nonneg_right hiCast hL
    exact intrinsicIter_norm (I := I) g hEnorm p hR hL ha hfit hloc
      c hc hcLen i.val (hiMul.trans_lt hNLa)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_family_of_nonzero_frameLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_family_of_nonzero_frameLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_family_of_nonzero_frameLift ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicIter_family_of_nonzero_frameLift

theorem intrinsicFiber_encard_ge_of_nonzero_frameLift
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (A : IntrinsicFrameLift (I := I) g hEnorm p c.extend 0 1)
    (hA : A.toFun 1 ≠ 0)
    (N : Nat) (hNLa : (N : Real) * L < a) :
    (N + 1 : ENat) ≤
      (intrinsicFiber (I := I) g hEnorm p p a).encard := by
  let points : Fin (N + 1) → intrinsicPullBall (E := E) R :=
    fun i =>
      ((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
        c hc hcLen)^[i.val]) (intrinsicZero (E := E) hR)
  have hfamily :
      Function.Injective points ∧
        (∀ i, intrinsicFramedExp (I := I) g hEnorm p (points i : E) = p) ∧
        ∀ i, ‖(points i : E)‖ ≤ (i.val : Real) * L := by
    simpa only [points] using
      (intrinsicIter_family_of_nonzero_frameLift (I := I) g hEnorm p hR h4aR
        hL ha hfit hloc hK hsmall hRm c hc hcLen A hA
        N hNLa)
  let pointsE : Fin (N + 1) → E := fun i => (points i : E)
  have hinjE : Function.Injective pointsE := by
    intro i j hij
    apply hfamily.1
    apply Subtype.ext
    exact hij
  have hrange :
      Set.range pointsE ⊆ intrinsicFiber (I := I) g hEnorm p p a := by
    rintro z ⟨i, rfl⟩
    constructor
    · rw [Metric.mem_ball, dist_zero_right]
      have hiN : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
      have hiCast : (i.val : Real) ≤ (N : Real) := by
        exact_mod_cast hiN
      have hiMul : (i.val : Real) * L ≤ (N : Real) * L :=
        mul_le_mul_of_nonneg_right hiCast hL
      exact hfamily.2.2 i |>.trans_lt (hiMul.trans_lt hNLa)
    · exact hfamily.2.1 i
  calc
    (N + 1 : ENat) = ENat.card (Fin (N + 1)) := by
      rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      norm_num
    _ ≤ (Set.range pointsE).encard := hinjE.encard_range
    _ ≤ (intrinsicFiber (I := I) g hEnorm p p a).encard :=
      Set.encard_le_encard hrange

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_encard_ge_of_nonzero_frameLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_encard_ge_of_nonzero_frameLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_encard_ge_of_nonzero_frameLift ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_encard_ge_of_nonzero_frameLift

theorem intrinsicFiber_encard_ge_of_riemannianEDist_lt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (A : IntrinsicFrameLift (I := I) g hEnorm p c.extend 0 1)
    (hA : A.toFun 1 ≠ 0)
    (N : Nat) (hNLa : (N : Real) * L < a)
    {q : M} {s : Real}
    (has : a + s < R)
    (hqs : _root_.Manifold.riemannianEDist I p q < ENNReal.ofReal s) :
    (N + 1 : ENat) ≤
      (intrinsicFiber (I := I) g hEnorm p q (a + s)).encard := by
  exact
    (intrinsicFiber_encard_ge_of_nonzero_frameLift (I := I) g hEnorm p hR h4aR
      hL ha hfit hloc hK hsmall hRm c hc hcLen A hA
      N hNLa).trans
      (fiber_encard_le (I := I) g hEnorm hqs has hloc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_encard_ge_of_riemannianEDist_lt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_encard_ge_of_riemannianEDist_lt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_encard_ge_of_riemannianEDist_lt ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_encard_ge_of_riemannianEDist_lt

theorem intrinsicFiber_encard_ge
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a r K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (A : IntrinsicFrameLift (I := I) g hEnorm p c.extend 0 1)
    (hA : A.toFun 1 ≠ 0)
    (N : Nat) (hr : 0 < r) (h2ra : 2 * r < a)
    (hNL : (N : Real) * L < r) :
    (N + 1 : ENat) ≤
      (intrinsicFiber (I := I) g hEnorm p p r).encard := by
  let points : Fin (N + 1) → intrinsicPullBall (E := E) R :=
    fun i =>
      ((loopTransportExt (I := I) g hEnorm p hL ha hfit hloc
        c hc hcLen)^[i.val]) (intrinsicZero (E := E) hR)
  have hfamily :
      Function.Injective points ∧
        (∀ i, intrinsicFramedExp (I := I) g hEnorm p (points i : E) = p) ∧
        ∀ i, ‖(points i : E)‖ ≤ (i.val : Real) * L := by
    simpa only [points] using
      (intrinsicIter_family (I := I) g hEnorm p hR h4aR
        hL ha hfit hloc hK hsmall hRm c hc hcLen A hA
        N hr h2ra hNL)
  let pointsE : Fin (N + 1) → E := fun i => (points i : E)
  have hinjE : Function.Injective pointsE := by
    intro i j hij
    apply hfamily.1
    apply Subtype.ext
    exact hij
  have hrange :
      Set.range pointsE ⊆ intrinsicFiber (I := I) g hEnorm p p r := by
    rintro z ⟨i, rfl⟩
    constructor
    · rw [Metric.mem_ball, dist_zero_right]
      have hiN : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
      have hiCast : (i.val : Real) ≤ (N : Real) := by
        exact_mod_cast hiN
      have hiMul : (i.val : Real) * L ≤ (N : Real) * L :=
        mul_le_mul_of_nonneg_right hiCast hL
      exact hfamily.2.2 i |>.trans_lt (hiMul.trans_lt hNL)
    · exact hfamily.2.1 i
  calc
    (N + 1 : ENat) = ENat.card (Fin (N + 1)) := by
      rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin]
      norm_num
    _ ≤ (Set.range pointsE).encard := hinjE.encard_range
    _ ≤ (intrinsicFiber (I := I) g hEnorm p p r).encard :=
      Set.encard_le_encard hrange

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_encard_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_encard_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_encard_ge ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_encard_ge

theorem intrinsicFiber_count_ge
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R L a r K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hL : 0 ≤ L) (ha : 0 ≤ a) (hfit : L + a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    (c : Path p p) (hc : Path.IsContMDiffWithSittingInstants (I := I) 1 c)
    (hcLen : Path.riemannianELength (I := I) c < ENNReal.ofReal L)
    (A : IntrinsicFrameLift (I := I) g hEnorm p c.extend 0 1)
    (hA : A.toFun 1 ≠ 0)
    (N : Nat) (hr : 0 < r) (h2ra : 2 * r < a)
    (hNL : (N : Real) * L < r)
    {q : M} {s : Real}
    (hrs : r + s < R)
    (hqs : _root_.Manifold.riemannianEDist I p q < ENNReal.ofReal s) :
    (N + 1 : ENat) ≤
      (intrinsicFiber (I := I) g hEnorm p q (r + s)).encard :=
  (intrinsicFiber_encard_ge (I := I) g hEnorm p hR h4aR
    hL ha hfit hloc hK hsmall hRm c hc hcLen A hA
    N hr h2ra hNL).trans
    (fiber_encard_le (I := I) g hEnorm hqs hrs hloc)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_count_ge then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_count_ge"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_count_ge ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicFiber_count_ge

attribute [-instance] Subtype.metricSpace Subtype.pseudoMetricSpace in
theorem intrinsicCore_center_fix
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R a K : Real} (hR : 0 < R) (h4aR : 4 * a < R)
    (hloc :
      IsLocalDiffeomorphOn 𝓘(Real, E) I ∞
        (intrinsicFramedExp (I := I) g hEnorm p)
        (Metric.ball (0 : E) R))
    (hK : 0 ≤ K)
    (hsmall : K * (2 * a) ^ 2 < (Real.pi / 2) ^ 2)
    (hRm :
      ∀ z : E, ‖z‖ < 3 * R / 4 →
        Real.sqrt (Tensor0SBundle.normSq0S (I := I) g
          (intrinsicFramedExp (I := I) g hEnorm p z) 4
          (Geometry.Curvature.metricRm04At
            (I := I) (M := M) g
            (intrinsicFramedExp (I := I) g hEnorm p z))) ≤ K)
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (points : ι → intrinsicPullBall (E := E) R)
    (hptsS : ∀ i : ι, points i ∈ intrinsicCore (E := E) R a)
    (T : intrinsicPullBall (E := E) R → intrinsicPullBall (E := E) R)
    (e : ι ≃ ι)
    (hmap : _root_.Set.MapsTo T (intrinsicCore (E := E) R a)
      (intrinsicCore (E := E) R a))
    (hperm : ∀ i : ι, T (points i) = points (e i)) :
    let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
    letI : _root_.Bundle.RiemannianBundle
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E
        (fun z : intrinsicPullBall (E := E) R ↦
          TangentSpace 𝓘(Real, E) z) :=
      ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
    letI : ConnectedSpace (intrinsicPullBall (E := E) R) :=
      Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
    letI : MetricSpace (intrinsicPullBall (E := E) R) :=
      HopfRinow.riemMetricSpace
        (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
    (∀ x ∈ intrinsicCore (E := E) R a,
      ∀ y ∈ intrinsicCore (E := E) R a,
        _root_.Dist.dist (T x) (T y) = _root_.Dist.dist x y) →
      ∃! c : intrinsicPullBall (E := E) R,
        c ∈ intrinsicCore (E := E) R a ∧
          (∀ z ∈ intrinsicCore (E := E) R a,
            CenterOfMass.metricEnergy (fun _ : ι => (1 : Real)) points c ≤
              CenterOfMass.metricEnergy (fun _ : ι => (1 : Real)) points z) ∧
          T c = c := by
  classical
  let gPull := intrinsicPullMetric (I := I) g hEnorm p hloc
  let : _root_.Bundle.RiemannianBundle
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E
      (fun z : intrinsicPullBall (E := E) R ↦
        TangentSpace 𝓘(Real, E) z) :=
    ⟨gPull.inner, gPull.contMDiff.continuous, by intro z v w; rfl⟩
  let : ConnectedSpace (intrinsicPullBall (E := E) R) :=
    Subtype.connectedSpace (_root_.Metric.isConnected_ball hR)
  let i₀ : ι := Classical.choice inferInstance
  have ha : 0 ≤ a :=
    (norm_nonneg (points i₀ : E)).trans (hptsS i₀)
  have haR : a < R := by linarith
  obtain ⟨c, hcS, hcminCE⟩ :=
    CenterOfMass.exists_minOn_compact
      (I := 𝓘(Real, E)) gPull (fun _ : ι => (1 : Real)) points
      (intrinsicCore_compact (E := E) haR) ⟨points i₀, hptsS i₀⟩
  let : MetricSpace (intrinsicPullBall (E := E) R) :=
    HopfRinow.riemMetricSpace
      (I := 𝓘(Real, E)) (M := intrinsicPullBall (E := E) R)
  change
    (∀ x ∈ intrinsicCore (E := E) R a,
      ∀ y ∈ intrinsicCore (E := E) R a,
        _root_.Dist.dist (T x) (T y) = _root_.Dist.dist x y) →
      ∃! c : intrinsicPullBall (E := E) R,
        c ∈ intrinsicCore (E := E) R a ∧
          (∀ z ∈ intrinsicCore (E := E) R a,
            CenterOfMass.metricEnergy (fun _ : ι => (1 : Real)) points c ≤
              CenterOfMass.metricEnergy (fun _ : ι => (1 : Real)) points z) ∧
          T c = c
  intro hdist
  obtain ⟨join, hjensen⟩ :=
    intrinsicCore_jensen (I := I) g hEnorm p hR h4aR hloc hK hsmall hRm
  have hcmin :
      ∀ z ∈ intrinsicCore (E := E) R a,
        CenterOfMass.metricEnergy (fun _ : ι => (1 : Real)) points c ≤
          CenterOfMass.metricEnergy (fun _ : ι => (1 : Real)) points z := by
    intro z hz
    rw [← CenterOfMass.centerEnergy_eq_dist
      (I := 𝓘(Real, E)) gPull (fun _ : ι => (1 : Real)) points c,
      ← CenterOfMass.centerEnergy_eq_dist
        (I := 𝓘(Real, E)) gPull (fun _ : ι => (1 : Real)) points z]
    exact hcminCE z hz
  have hstrict :
      CenterOfMass.StrictMidConvexOn join (intrinsicCore (E := E) R a)
        (CenterOfMass.metricEnergy (fun _ : ι => (1 : Real)) points) :=
    CenterOfMass.metricEnergy_strict
      (fun _ : ι => (1 : Real)) points
      (fun _ => by norm_num) ⟨i₀, by norm_num⟩
      (fun i => hjensen (points i) (hptsS i))
  have hTcS : T c ∈ intrinsicCore (E := E) R a := hmap hcS
  have hTcmin :
      ∀ z ∈ intrinsicCore (E := E) R a,
        CenterOfMass.metricEnergy (fun _ : ι => (1 : Real)) points (T c) ≤
          CenterOfMass.metricEnergy (fun _ : ι => (1 : Real)) points z := by
    intro z hz
    rw [CenterOfMass.metricEnergy_perm
      (fun _ : ι => (1 : Real)) points T e
      (fun _ => rfl) hperm hptsS hdist hcS]
    exact hcmin z hz
  have hfix : T c = c :=
    CenterOfMass.min_unique_of_mid hstrict hTcS hcS hTcmin hcmin
  refine ⟨c, ⟨hcS, hcmin, hfix⟩, ?_⟩
  intro y hy
  exact CenterOfMass.min_unique_of_mid
    hstrict hy.1 hcS hy.2.1 hcmin

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCore_center_fix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCore_center_fix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCore_center_fix ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.intrinsicCore_center_fix

end CheegerGromovTaylor
end Riemannian
end Geometry
end DifferentialGeometry
