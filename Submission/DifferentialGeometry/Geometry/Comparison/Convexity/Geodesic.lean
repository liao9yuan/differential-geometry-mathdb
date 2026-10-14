import Submission.DifferentialGeometry.Geometry.Exponential.GaussLemma.Basic
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Basic
import Submission.DifferentialGeometry.Geometry.Exponential.Intrinsic.Geodesic.Continuity
import Submission.DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import Submission.DifferentialGeometry.Geometry.Metric.Completeness
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.UnitInterval

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Connection


open _root_.Set _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold
open scoped _root_.Topology _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.ENNReal

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

def IsGeodesicallyConvexWith {M : Type*} [TopologicalSpace M]
    (join : M → M → ℝ → M) (S : Set M) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S,
    ContinuousOn (join a b) unitInterval ∧ join a b 0 = a ∧ join a b 1 = b ∧
      (∀ t ∈ unitInterval, join a b t ∈ S)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith ``Submission.DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith

namespace IsGeodesicallyConvexWith

variable {M : Type*} [TopologicalSpace M] {join : M → M → ℝ → M} {S T : Set M}

theorem joinedIn (hS : IsGeodesicallyConvexWith join S) {a b : M}
    (ha : a ∈ S) (hb : b ∈ S) : JoinedIn S a b := by
  obtain ⟨hcont, h0, h1, hmem⟩ := hS a ha b hb
  refine JoinedIn.ofLine hcont h0 h1 ?_
  rintro x ⟨t, ht, rfl⟩
  exact hmem t ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith.joinedIn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith.joinedIn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith.joinedIn ``Submission.DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith.joinedIn

theorem inter (hS : IsGeodesicallyConvexWith join S)
    (hT : IsGeodesicallyConvexWith join T) :
    IsGeodesicallyConvexWith join (S ∩ T) := by
  rintro a ⟨haS, haT⟩ b ⟨hbS, hbT⟩
  obtain ⟨hcontS, h0, h1, hmemS⟩ := hS a haS b hbS
  obtain ⟨_, _, _, hmemT⟩ := hT a haT b hbT
  exact ⟨hcontS, h0, h1, fun t ht => ⟨hmemS t ht, hmemT t ht⟩⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith.inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith.inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith.inter ``Submission.DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith.inter

theorem joinedIn_inter (hS : IsGeodesicallyConvexWith join S)
    (hT : IsGeodesicallyConvexWith join T) {a b : M}
    (haS : a ∈ S) (haT : a ∈ T) (hbS : b ∈ S) (hbT : b ∈ T) :
    JoinedIn (S ∩ T) a b :=
  (hS.inter hT).joinedIn ⟨haS, haT⟩ ⟨hbS, hbT⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith.joinedIn_inter then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith.joinedIn_inter"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith.joinedIn_inter ``Submission.DifferentialGeometry.Geometry.Riemannian.IsGeodesicallyConvexWith.joinedIn_inter

end IsGeodesicallyConvexWith

section IntrinsicBall

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential
open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Geodesic
open _root_.Submission.DifferentialGeometry.Integral.Measure

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
variable [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]

def smallNormalBall (p : M) (ρ : ℝ) : Set M :=
  {q : M | _root_.Manifold.riemannianEDist I p q < ENNReal.ofReal ρ}

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.smallNormalBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.smallNormalBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.smallNormalBall ``Submission.DifferentialGeometry.Geometry.Riemannian.smallNormalBall

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
@[simp] lemma mem_smallNormalBall {p q : M} {ρ : ℝ} :
    q ∈ smallNormalBall (I := I) p ρ ↔ _root_.Manifold.riemannianEDist I p q < ENNReal.ofReal ρ :=
  Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.mem_smallNormalBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.mem_smallNormalBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.mem_smallNormalBall ``Submission.DifferentialGeometry.Geometry.Riemannian.mem_smallNormalBall

omit [Module.Finite ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] in
lemma centre_mem_smallNormalBall (p : M) {ρ : ℝ} (hρ : 0 < ρ) :
    p ∈ smallNormalBall (I := I) p ρ := by
  rw [mem_smallNormalBall, _root_.Manifold.riemannianEDist_self]
  exact ENNReal.ofReal_pos.2 hρ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.centre_mem_smallNormalBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.centre_mem_smallNormalBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.centre_mem_smallNormalBall ``Submission.DifferentialGeometry.Geometry.Riemannian.centre_mem_smallNormalBall

variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [T2Space (TangentBundle I M)]
  [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]

noncomputable def minimizingVec
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (a b : M) : TangentSpace I a :=
  Classical.choose
    (hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) g hEnorm a b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.minimizingVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.minimizingVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.minimizingVec ``Submission.DifferentialGeometry.Geometry.Riemannian.minimizingVec

theorem minimizingVec_exp
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (a b : M) :
    expMapIntrinsic (I := I) g hEnorm a (minimizingVec (I := I) g hEnorm a b) = b :=
  (Classical.choose_spec
    (hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) g hEnorm a b)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.minimizingVec_exp then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.minimizingVec_exp"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.minimizingVec_exp ``Submission.DifferentialGeometry.Geometry.Riemannian.minimizingVec_exp

theorem minimizingVec_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (a b : M) :
    Real.sqrt (g.inner a (minimizingVec (I := I) g hEnorm a b)
        (minimizingVec (I := I) g hEnorm a b)) =
      (_root_.Manifold.riemannianEDist I a b).toReal :=
  (Classical.choose_spec
    (hopf_rinow_expMapIntrinsic_surjective_minimizing
      (I := I) g hEnorm a b)).2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.minimizingVec_len then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.minimizingVec_len"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.minimizingVec_len ``Submission.DifferentialGeometry.Geometry.Riemannian.minimizingVec_len

noncomputable def minJoin
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (a b : M) (t : ℝ) : M :=
  intrinsicGeodesic (I := I) g hEnorm a
    (minimizingVec (I := I) g hEnorm a b) t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.minJoin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.minJoin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.minJoin ``Submission.DifferentialGeometry.Geometry.Riemannian.minJoin

@[simp] theorem minJoin_zero
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (a b : M) : minJoin (I := I) g hEnorm a b 0 = a := by
  exact intrinsicGeodesic_zero (I := I) g hEnorm a
    (minimizingVec (I := I) g hEnorm a b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.minJoin_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.minJoin_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.minJoin_zero ``Submission.DifferentialGeometry.Geometry.Riemannian.minJoin_zero

@[simp] theorem minJoin_one
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (a b : M) : minJoin (I := I) g hEnorm a b 1 = b := by
  change intrinsicGeodesic (I := I) g hEnorm a
    (minimizingVec (I := I) g hEnorm a b) 1 = b
  rw [← expMapIntrinsic_def, minimizingVec_exp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.minJoin_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.minJoin_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.minJoin_one ``Submission.DifferentialGeometry.Geometry.Riemannian.minJoin_one

theorem minJoin_cont
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (a b : M) : Continuous (minJoin (I := I) g hEnorm a b) :=
  intrinsicGeodesic_continuous (I := I) g hEnorm a
    (minimizingVec (I := I) g hEnorm a b)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.minJoin_cont then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.minJoin_cont"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.minJoin_cont ``Submission.DifferentialGeometry.Geometry.Riemannian.minJoin_cont

theorem minJoin_edist_le
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (a b : M) {t : ℝ} (ht : 0 ≤ t) :
    riemannianEDist I a (minJoin (I := I) g hEnorm a b t) ≤
      ENNReal.ofReal ((_root_.Manifold.riemannianEDist I a b).toReal * t) := by
  simpa only [minJoin, intrinsicGeodesic_zero, minimizingVec_len, sub_zero] using
    intrinsicGeodesic_riemannianEDist_le
      (I := I) g hEnorm a (minimizingVec (I := I) g hEnorm a b)
        (s := 0) (t := t) ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.minJoin_edist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.minJoin_edist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.minJoin_edist_le ``Submission.DifferentialGeometry.Geometry.Riemannian.minJoin_edist_le

theorem minJoin_arcLength
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (a b : M) :
    Variation.arcLength (I := I) g (minJoin (I := I) g hEnorm a b) 0 1 =
      (_root_.Manifold.riemannianEDist I a b).toReal := by
  have harc :
      Variation.arcLength (I := I) g
          (intrinsicGeodesic (I := I) g hEnorm a
            (minimizingVec (I := I) g hEnorm a b)) 0 1 =
        Real.sqrt
          (g.inner a (minimizingVec (I := I) g hEnorm a b)
            (minimizingVec (I := I) g hEnorm a b)) := by
    have hI :
        Variation.arcLength (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm a
              (minimizingVec (I := I) g hEnorm a b)) 0 1 =
          ∫ _t in (0 : ℝ)..1,
            Real.sqrt
              (g.inner a (minimizingVec (I := I) g hEnorm a b)
                (minimizingVec (I := I) g hEnorm a b)) := by
      unfold Variation.arcLength
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      congr 1
      exact intrinsicGeodesic_speedSq_eq (I := I) g hEnorm a
        (minimizingVec (I := I) g hEnorm a b) t
    rw [hI, intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  change Variation.arcLength (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm a
        (minimizingVec (I := I) g hEnorm a b)) 0 1 =
    (_root_.Manifold.riemannianEDist I a b).toReal
  rw [harc, minimizingVec_len]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.minJoin_arcLength then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.minJoin_arcLength"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.minJoin_arcLength ``Submission.DifferentialGeometry.Geometry.Riemannian.minJoin_arcLength

theorem minJoin_pathLen
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (a b : M) :
    Manifold.pathELength I (minJoin (I := I) g hEnorm a b) 0 1 =
      ENNReal.ofReal ((_root_.Manifold.riemannianEDist I a b).toReal) := by
  let γ : ℝ → M := minJoin (I := I) g hEnorm a b
  have hγC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 1) := by
    exact
      (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm a
        (minimizingVec (I := I) g hEnorm a b)).mono
        (Set.subset_univ _)
  rw [Geodesic.pathELength_eq_arcLength_riemannianBundle (I := I) g zero_le_one
      (Geodesic.speedSqrt_integrableOn_Icc_of_C1
        (I := I) g zero_le_one hγC1)
      (fun t _ => hEnorm (γ t)
        (mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)))]
  change ENNReal.ofReal
      (Variation.arcLength (I := I) g
        (minJoin (I := I) g hEnorm a b) 0 1) =
    ENNReal.ofReal ((_root_.Manifold.riemannianEDist I a b).toReal)
  rw [minJoin_arcLength (I := I) g hEnorm a b]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.minJoin_pathLen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.minJoin_pathLen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.minJoin_pathLen ``Submission.DifferentialGeometry.Geometry.Riemannian.minJoin_pathLen

omit [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
private lemma intrinsicGeodesic_speedSq_const
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    g.inner (intrinsicGeodesic (I := I) g hEnorm p v t)
        (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) t 1)
        (mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) t 1)
      = g.inner p v v := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hgeo : IsGeodesic (I := I) g γ :=
    intrinsicGeodesic_isGeodesic (I := I) g hEnorm p v
  have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ Set.univ :=
    intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v
  have hconst := HopfRinow.isGeodesicOn_speedSq_const (I := I) g (t₀ := t) (t₁ := 0)
    isOpen_univ (hgeo.isGeodesicOn Set.univ) hC1 (Set.subset_univ _)
  rw [hconst]
  have h0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hvelE : (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = (v : E) :=
    intrinsicGeodesic_mfderiv_zero (I := I) g hEnorm p v
  exact congrArg₂ (fun (x : M) (w : E) => g.inner x w w) h0 hvelE

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.intrinsicGeodesic_speedSq_const
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.intrinsicGeodesic_speedSq_const target :: scope.openDecls } }

omit [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
private lemma intrinsicGeodesic_velocity_enorm_le'
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    ‖mfderiv 𝓘(ℝ, ℝ) I (intrinsicGeodesic (I := I) g hEnorm p v) t (1 : ℝ)‖ₑ
      ≤ ENNReal.ofReal (Real.sqrt (g.inner p v v)) := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hnn : (0 : ℝ) ≤ g.inner p v v := by
    rcases eq_or_ne v 0 with h | h
    · subst h; simp
    · exact (g.pos p v h).le
  set c : ℝ := Real.sqrt (g.inner p v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have hspeedSq : g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = c ^ 2 := by
    rw [intrinsicGeodesic_speedSq_const (I := I) g hEnorm p v t, hc_def,
      Real.sq_sqrt hnn]
  rw [hEnorm]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  calc Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1))
      = Real.sqrt (c ^ 2) := by rw [hspeedSq]
    _ = c := Real.sqrt_sq hc_nn

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.intrinsicGeodesic_velocity_enorm_le'
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.intrinsicGeodesic_velocity_enorm_le' target :: scope.openDecls } }

omit [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
theorem intrinsicGeodesic_riemannianEDist_le_radius
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) {t : ℝ} (ht : 0 ≤ t) :
    riemannianEDist I p (intrinsicGeodesic (I := I) g hEnorm p v t)
      ≤ ENNReal.ofReal (Real.sqrt (g.inner p v v) * t) := by
  let : MeasurableSpace M := borel M
  have : BorelSpace M := ⟨rfl⟩
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  set c : ℝ := Real.sqrt (g.inner p v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have hγ0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hγ_C1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Set.Icc 0 t) :=
    (intrinsicGeodesic_contMDiffOn (I := I) g hEnorm p v).mono (Set.subset_univ _)
  have h_pathLen_le : _root_.Manifold.pathELength I γ 0 t ≤ ENNReal.ofReal (c * t) := by
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    have h_le :
        ∫⁻ τ in Set.Icc 0 t, (fun τ => ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ) τ
          ≤ ∫⁻ _ in Set.Icc 0 t, ENNReal.ofReal c := by
      refine MeasureTheory.setLIntegral_mono' measurableSet_Icc (fun τ _ => ?_)
      simpa [hγ_def, hc_def] using
        intrinsicGeodesic_velocity_enorm_le' (I := I) g hEnorm p v τ
    have h_const :
        (∫⁻ _ in Set.Icc 0 t, ENNReal.ofReal c)
          = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc 0 t) :=
      MeasureTheory.setLIntegral_const (Set.Icc 0 t) (ENNReal.ofReal c)
    have h_vol : MeasureTheory.volume (Set.Icc 0 t) = ENNReal.ofReal (t - 0) :=
      Real.volume_Icc
    calc
      ∫⁻ τ in Set.Icc 0 t, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ (1 : ℝ)‖ₑ
          ≤ ∫⁻ _ in Set.Icc 0 t, ENNReal.ofReal c := h_le
      _ = ENNReal.ofReal c * MeasureTheory.volume (Set.Icc 0 t) := h_const
      _ = ENNReal.ofReal c * ENNReal.ofReal (t - 0) := by rw [h_vol]
      _ = ENNReal.ofReal (c * (t - 0)) := (ENNReal.ofReal_mul hc_nn).symm
      _ = ENNReal.ofReal (c * t) := by ring_nf
  have h_dist_le : _root_.Manifold.riemannianEDist I (γ 0) (γ t) ≤ _root_.Manifold.pathELength I γ 0 t :=
    riemannianEDist_le_pathELength (I := I) (γ := γ) (a := 0) (b := t)
      hγ_C1 rfl rfl ht
  calc _root_.Manifold.riemannianEDist I p (γ t)
      = _root_.Manifold.riemannianEDist I (γ 0) (γ t) := by rw [hγ0]
    _ ≤ _root_.Manifold.pathELength I γ 0 t := h_dist_le
    _ ≤ ENNReal.ofReal (c * t) := h_pathLen_le

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.intrinsicGeodesic_riemannianEDist_le_radius then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.intrinsicGeodesic_riemannianEDist_le_radius"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.intrinsicGeodesic_riemannianEDist_le_radius ``Submission.DifferentialGeometry.Geometry.Riemannian.intrinsicGeodesic_riemannianEDist_le_radius

omit [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
theorem smallNormalBall_radial_confined
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) {ρ : ℝ}
    (hv : Real.sqrt (g.inner p v v) < ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    intrinsicGeodesic (I := I) g hEnorm p v t ∈ smallNormalBall (I := I) p ρ := by
  obtain ⟨ht0, ht1⟩ := ht
  set c : ℝ := Real.sqrt (g.inner p v v) with hc_def
  have hc_nn : (0 : ℝ) ≤ c := Real.sqrt_nonneg _
  have hbound := intrinsicGeodesic_riemannianEDist_le_radius (I := I) g hEnorm p v ht0
  rw [mem_smallNormalBall]
  refine lt_of_le_of_lt hbound ?_
  refine lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_)
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hc_nn |>.2 hv)
  calc c * t ≤ c * 1 := by
        exact mul_le_mul_of_nonneg_left ht1 hc_nn
    _ = c := mul_one c

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.smallNormalBall_radial_confined then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.smallNormalBall_radial_confined"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.smallNormalBall_radial_confined ``Submission.DifferentialGeometry.Geometry.Riemannian.smallNormalBall_radial_confined

omit [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
theorem joinedIn_centre_smallNormalBall
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (v : TangentSpace I p) {ρ : ℝ}
    (hv : Real.sqrt (g.inner p v v) < ρ) :
    JoinedIn (smallNormalBall (I := I) p ρ) p
      (expMapIntrinsic (I := I) g hEnorm p v) := by
  set γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm p v with hγ_def
  have hγ_cont : Continuous γ := intrinsicGeodesic_continuous (I := I) g hEnorm p v
  have hγ0 : γ 0 = p := intrinsicGeodesic_zero (I := I) g hEnorm p v
  have hγ1 : γ 1 = expMapIntrinsic (I := I) g hEnorm p v := rfl
  refine JoinedIn.ofLine hγ_cont.continuousOn hγ0 hγ1 ?_
  rintro x ⟨t, ht, rfl⟩
  exact smallNormalBall_radial_confined (I := I) g hEnorm p v hv ht

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.joinedIn_centre_smallNormalBall then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.joinedIn_centre_smallNormalBall"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.joinedIn_centre_smallNormalBall ``Submission.DifferentialGeometry.Geometry.Riemannian.joinedIn_centre_smallNormalBall

omit [RiemannianBundle (fun x : M => TangentSpace I x)]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [T2Space (TangentBundle I M)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] in
omit [ConnectedSpace M] in
theorem joinedIn_centre_smallNormalBall_of_complete_metric
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (p : M) (v : TangentSpace I p) {ρ : ℝ}
    (hv : Real.sqrt (g.inner p v v) < ρ) :
    letI : IsManifold I 1 M :=
      IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    letI : TopologicalSpace.MetrizableSpace M :=
      Manifold.metrizableSpace I M
    letI : T3Space M := inferInstance
    letI : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    letI : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
    letI : CompleteSpace M := hcomplete.complete
    let hEnorm : IsMetricNorm (I := I) (M := M) g :=
      fun x w => tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x w
    JoinedIn (smallNormalBall (I := I) p ρ) p
      (expMapIntrinsic (I := I) g hEnorm p v) := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : _root_.Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := (EMetricSpace.ofRiemannianMetric I M).toPseudoEMetricSpace
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x w
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x w
  exact joinedIn_centre_smallNormalBall (I := I) (M := M) g hEnorm p v hv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.joinedIn_centre_smallNormalBall_of_complete_metric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.joinedIn_centre_smallNormalBall_of_complete_metric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.joinedIn_centre_smallNormalBall_of_complete_metric ``Submission.DifferentialGeometry.Geometry.Riemannian.joinedIn_centre_smallNormalBall_of_complete_metric

end IntrinsicBall

end Riemannian
end Geometry
end DifferentialGeometry

end
