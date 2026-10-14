import Submission.DifferentialGeometry.Analysis.Parabolic.Bernstein.Cutoff

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

namespace DifferentialGeometry.PDE.RicciFlow

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Set
open _root_.Submission.DifferentialGeometry.Analysis.Parabolic
open scoped _root_.Manifold _root_.ContDiff _root_.Topology _root_.Bundle _root_.Submission.Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

structure ShiCutoffData
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real) where
  chi : Nat → Real → M → Real
  err : Nat → Real
  support : Nat → Set M
  err_nonneg : ∀ n, 0 ≤ err n
  err_tendsto : _root_.Filter.Tendsto err _root_.Filter.atTop (nhds 0)
  support_compact : ∀ n, IsCompact (support n)
  support_zero :
    ∀ n t, t ∈ Set.Icc 0 T → ∀ x, x ∉ support n → chi n t x = 0
  range :
    ∀ n t x, t ∈ Set.Icc 0 T → chi n t x ∈ Set.Icc (0 : Real) 1
  exhausts :
    ∀ t x, t ∈ Set.Icc 0 T →
      ∃ n₀, ∀ n, n₀ ≤ n → chi n t x = 1
  joint_cont :
    ∀ n, ContinuousOn
      (fun p : Real × M => chi n p.1 p.2) (spacetimeSlab (M := M) T)
  time_diff :
    ∀ n t, t ∈ Set.Icc 0 T → 0 < t → ∀ x,
      DifferentiableWithinAt Real (fun s => chi n s x) (Set.Icc 0 T) t
  space_smooth :
    ∀ n t, t ∈ Set.Icc 0 T →
      ContMDiff I 𝓘(Real, Real) ∞ (chi n t)
  grad_sq_le :
    ∀ n t, t ∈ Set.Icc 0 T → 0 < t → ∀ x,
      (G.metric t).inner x
          (gradientFun (I := I) (G.metric t) (chi n t) x)
          (gradientFun (I := I) (G.metric t) (chi n t) x) ≤
        err n * chi n t x
  parabolic_le :
    ∀ n t, t ∈ Set.Icc 0 T → 0 < t → ∀ x,
      parabolicOperatorWithDrift (I := I) G T
        (fun _ y => (0 : TangentSpace I y)) (chi n) t x ≤ err n

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ShiCutoffData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ShiCutoffData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ShiCutoffData ``Submission.DifferentialGeometry.PDE.RicciFlow.ShiCutoffData

structure ShiBarrierCutoffData
    (G : MetricConnectionFamily (I := I) (M := M) Real)
    (T : Real)
    (O : M) where
  chi : Nat → Real → M → Real
  err : Nat → Real
  support : Nat → Set M
  err_nonneg : ∀ n, 0 ≤ err n
  err_tendsto : _root_.Filter.Tendsto err _root_.Filter.atTop (nhds 0)
  support_compact : ∀ n, IsCompact (support n)
  support_zero :
    ∀ n t, t ∈ Set.Icc 0 T →
      ∀ x, x ∉ support n → chi n t x = 0
  range :
    ∀ n t x, t ∈ Set.Icc 0 T →
      chi n t x ∈ Set.Icc (0 : Real) 1
  center_exhausts :
    ∀ t, t ∈ Set.Icc 0 T →
      ∀ᶠ n in _root_.Filter.atTop, chi n t O = 1
  joint_cont :
    ∀ n, ContinuousOn
      (fun p : Real × M => chi n p.1 p.2)
      (Set.Icc 0 T ×ˢ support n)
  lowerSupport :
    ∀ n t, t ∈ Set.Icc 0 T → 0 < t → ∀ x,
      0 < chi n t x →
        ShiCutoffLowerSupportAt
          (I := I) G T (err n) (chi n) t x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ShiBarrierCutoffData then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ShiBarrierCutoffData"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ShiBarrierCutoffData ``Submission.DifferentialGeometry.PDE.RicciFlow.ShiBarrierCutoffData

namespace ShiCutoffData

theorem support_slab
    {G : MetricConnectionFamily (I := I) (M := M) Real} {T : Real}
    (cut : ShiCutoffData (I := I) G T) (n : Nat) :
    IsCompact (Set.Icc 0 T ×ˢ cut.support n) :=
  isCompact_Icc.prod (cut.support_compact n)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.support_slab then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.support_slab"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.support_slab ``Submission.DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.support_slab

theorem space_diff
    {G : MetricConnectionFamily (I := I) (M := M) Real} {T : Real}
    (cut : ShiCutoffData (I := I) G T) {n : Nat} {t : Real}
    (ht : t ∈ Set.Icc 0 T) (x : M) :
    MDifferentiableAt I 𝓘(Real, Real) (cut.chi n t) x :=
  (cut.space_smooth n t ht).mdifferentiableAt (by simp)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.space_diff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.space_diff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.space_diff ``Submission.DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.space_diff

theorem grad_diff
    {G : MetricConnectionFamily (I := I) (M := M) Real} {T : Real}
    (cut : ShiCutoffData (I := I) G T) {n : Nat} {t : Real}
    (ht : t ∈ Set.Icc 0 T) (x : M) :
    MDifferentiableAt I (I.prod 𝓘(Real, E))
      (T% fun y : M =>
        gradientFun (I := I) (G.metric t) (cut.chi n t) y) x :=
  gradientFun_mdiffAt (I := I) (G.metric t) (cut.space_smooth n t ht) x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.grad_diff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.grad_diff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.grad_diff ``Submission.DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.grad_diff

def toBarrierAt
    {G : MetricConnectionFamily (I := I) (M := M) Real} {T : Real}
    (cut : ShiCutoffData (I := I) G T) (O : M) :
    ShiBarrierCutoffData (I := I) G T O where
  chi := cut.chi
  err := cut.err
  support := cut.support
  err_nonneg := cut.err_nonneg
  err_tendsto := cut.err_tendsto
  support_compact := cut.support_compact
  support_zero := cut.support_zero
  range := cut.range
  center_exhausts := by
    intro t ht
    obtain ⟨n₀, hn₀⟩ := cut.exhausts t O ht
    filter_upwards [_root_.Filter.eventually_ge_atTop n₀] with n hn
    exact hn₀ n hn
  joint_cont := by
    intro n
    exact (cut.joint_cont n).mono fun p hp =>
      ⟨hp.1, Set.mem_univ p.2⟩
  lowerSupport := by
    intro n t ht htpos x _hx
    refine
      { phi := cut.chi n
        eq_at := rfl
        lower_nhds := ?_
        time_diff := cut.time_diff n t ht htpos x
        space_diff_nhds := ?_
        grad_diff := cut.grad_diff ht x
        grad_sq_le := cut.grad_sq_le n t ht htpos x
        parabolic_le := cut.parabolic_le n t ht htpos x }
    · filter_upwards [self_mem_nhdsWithin] with p hp
      exact ⟨(cut.range n p.1 p.2 hp.1).1, le_rfl⟩
    · exact Filter.Eventually.of_forall fun y => cut.space_diff ht y

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.toBarrierAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.toBarrierAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.toBarrierAt ``Submission.DifferentialGeometry.PDE.RicciFlow.ShiCutoffData.toBarrierAt

end ShiCutoffData

end DifferentialGeometry.PDE.RicciFlow
