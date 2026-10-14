import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Ramps
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.Set _root_.Submission.Set _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

section

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def CurveMap.sweptDensity (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M)
    (J : Set ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    Real.sqrt (c.normSq g (c.velocity (I := I) J) x t) * c.speed g x t

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.sweptDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.sweptDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.sweptDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.sweptDensity

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem CurveMap.sweptDensity_nonneg (c : CurveMap M)
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (t : ℝ) :
    0 ≤ c.sweptDensity g J t := by
  apply intervalIntegral.integral_nonneg_of_forall (by norm_num : (0 : ℝ) ≤ 1)
  intro x
  exact mul_nonneg (Real.sqrt_nonneg _) (c.speed_nonneg g x t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.sweptDensity_nonneg then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.sweptDensity_nonneg"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.sweptDensity_nonneg ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.sweptDensity_nonneg

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
private theorem inner_congr_of_base_eq (g : SmoothRiemannianMetric I M) {a b : M}
    {v w : TangentSpace I a} {v' w' : TangentSpace I b}
    (hab : a = b) (hv : v = v') (hw : w = w') :
    g.inner a v w = g.inner b v' w' := by
  subst hab
  rw [hv, hw]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.inner_congr_of_base_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.inner_congr_of_base_eq target :: scope.openDecls } }

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
theorem CurveMap.sweptDensity_congr {c d : CurveMap M}
    {g : ℝ → SmoothRiemannianMetric I M} {J : Set ℝ}
    (h : ∀ z t, t ∈ J → c z t = d z t) (t : ℝ) (ht : t ∈ J) :
    c.sweptDensity g J t = d.sweptDensity g J t := by
  unfold CurveMap.sweptDensity
  refine intervalIntegral.integral_congr (fun x _ => ?_)
  have hbase : c.lift x t = d.lift x t := h (x : AddCircle (1 : ℝ)) t ht
  have hev : (c.lift x) =ᶠ[𝓝[J] t] (d.lift x) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact h (x : AddCircle (1 : ℝ)) y hy
  have hmd : mfderivWithin 𝓘(ℝ, ℝ) I (c.lift x) J t =
      mfderivWithin 𝓘(ℝ, ℝ) I (d.lift x) J t := hev.mfderivWithin_eq hbase
  have hvel : c.velocity (I := I) J x t = d.velocity (I := I) J x t := by
    unfold CurveMap.velocity
    rw [hmd]
    rfl
  have hXfun : (fun y : ℝ => c.lift y t) = (fun y : ℝ => d.lift y t) :=
    funext (fun y => h (y : AddCircle (1 : ℝ)) t ht)
  have hX : c.X (I := I) x t = d.X (I := I) x t := by
    unfold CurveMap.X
    rw [hXfun]
    rfl
  have hinner : (g t).inner (c.lift x t) (c.velocity (I := I) J x t)
        (c.velocity (I := I) J x t) =
      (g t).inner (d.lift x t) (d.velocity (I := I) J x t)
        (d.velocity (I := I) J x t) :=
    inner_congr_of_base_eq (g t) hbase hvel hvel
  have hnorm : c.normSq g (c.velocity (I := I) J) x t =
      d.normSq g (d.velocity (I := I) J) x t := by
    simpa only [CurveMap.normSq] using hinner
  have hinnerX : (g t).inner (c.lift x t) (c.X (I := I) x t) (c.X (I := I) x t) =
      (g t).inner (d.lift x t) (d.X (I := I) x t) (d.X (I := I) x t) :=
    inner_congr_of_base_eq (g t) hbase hX hX
  have hsp : c.speed g x t = d.speed g x t := by
    simpa only [CurveMap.speed] using congrArg Real.sqrt hinnerX
  rw [hnorm, hsp]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.sweptDensity_congr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.sweptDensity_congr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.sweptDensity_congr ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.sweptDensity_congr

variable [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
variable {D : RealTimeInterval} {a b : ℝ}

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem CurveMap.continuousOn_sweptIntegrand
    (B : RicciBackground (I := I) (M := M) D a b)
    (c : CurveMap M) (hc : c.SmoothOn (I := I) (_root_.Set.Icc a b)) :
    ContinuousOn (fun p : ℝ × ℝ =>
      Real.sqrt (c.normSq B.family.metric (c.velocity (I := I) (_root_.Set.Icc a b)) p.1 p.2) *
        c.speed B.family.metric p.1 p.2) (_root_.Set.univ ×ˢ _root_.Set.Icc a b) := by
  have hJ : UniqueDiffOn ℝ (_root_.Set.Icc a b) := uniqueDiffOn_Icc B.lt
  have hV : CurveMap.Field.SmoothOn (I := I)
      (c.velocity (I := I) (_root_.Set.Icc a b)) (_root_.Set.Icc a b) :=
    CurveMap.Field.smoothOn_velocity c hc hJ
  have hnorm : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      (c).normSq B.family.metric
        (c.velocity (I := I) (_root_.Set.Icc a b)) p.1 p.2) (_root_.Set.univ ×ˢ _root_.Set.Icc a b) :=
    CurveMap.Field.smoothOn_inner B.family.metric B.smooth B.regular c hc
      _ _ hV hV
  have hX : CurveMap.Field.SmoothOn (I := I) (c.X) (_root_.Set.Icc a b) :=
    CurveMap.Field.smoothOn_X c (_root_.Set.Icc a b) hc
  have hinnerX : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ =>
      (B.family.metric p.2).inner (c.lift p.1 p.2)
        (c.X (I := I) p.1 p.2)
        (c.X (I := I) p.1 p.2)) (_root_.Set.univ ×ˢ _root_.Set.Icc a b) :=
    CurveMap.Field.smoothOn_inner B.family.metric B.smooth B.regular c hc
      _ _ hX hX
  have hspeed : ContinuousOn (fun p : ℝ × ℝ =>
      c.speed B.family.metric p.1 p.2) (_root_.Set.univ ×ˢ _root_.Set.Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn hinnerX.continuousOn
  have hsqrt : ContinuousOn (fun p : ℝ × ℝ =>
      Real.sqrt ((c).normSq B.family.metric
        (c.velocity (I := I) (_root_.Set.Icc a b)) p.1 p.2)) (_root_.Set.univ ×ˢ _root_.Set.Icc a b) :=
    Real.continuous_sqrt.comp_continuousOn hnorm.continuousOn
  exact hsqrt.mul hspeed

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.continuousOn_sweptIntegrand then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.continuousOn_sweptIntegrand"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.continuousOn_sweptIntegrand ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.CurveMap.continuousOn_sweptIntegrand


omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem continuousOn_sweptDensity (B : RicciBackground (I := I) (M := M) D a b)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (_root_.Set.Icc a b)) :
    ContinuousOn (fun t => (curveOfLoopFamily γ).sweptDensity B.family.metric (_root_.Set.Icc a b) t)
      (_root_.Set.Icc a b) := by
  exact continuousOn_intervalIntegral_of_continuousOn_rectangle B.lt.le
    (((curveOfLoopFamily γ).continuousOn_sweptIntegrand B hγ).mono
      (Set.prod_mono (_root_.Set.subset_univ _) subset_rfl))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_sweptDensity then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_sweptDensity"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_sweptDensity ``Submission.DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.continuousOn_sweptDensity

end

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
