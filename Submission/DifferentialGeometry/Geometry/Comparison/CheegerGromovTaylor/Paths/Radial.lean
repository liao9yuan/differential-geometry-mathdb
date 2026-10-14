import Submission.DifferentialGeometry.Geometry.Comparison.CheegerGromovTaylor.Paths.ExponentialLift
import Submission.DifferentialGeometry.Geometry.Exponential.RadialPath

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Filter _root_.Function _root_.Manifold _root_.Submission.Manifold _root_.Set
open scoped _root_.ContDiff _root_.ENNReal _root_.Manifold _root_.Submission.Manifold _root_.Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace CheegerGromovTaylor

open _root_.Submission.DifferentialGeometry.Geometry.Riemannian.Exponential _root_.Submission.DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

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

private noncomputable def flatTime (t : Real) : Real :=
  Real.smoothTransition (3 * t - 1)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.flatTime
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.flatTime target :: scope.openDecls } }

private theorem flatTime_zero : flatTime 0 = 0 := by
  rw [flatTime, Real.smoothTransition.zero_of_nonpos (by norm_num)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.flatTime_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.flatTime_zero target :: scope.openDecls } }

private theorem flatTime_one : flatTime 1 = 1 := by
  rw [flatTime, Real.smoothTransition.one_of_one_le (by norm_num)]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.flatTime_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.flatTime_one target :: scope.openDecls } }

private theorem flatTime_cd : ContDiff Real ∞ flatTime := by
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.mul contDiff_id |>.sub contDiff_const)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.flatTime_cd
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.flatTime_cd target :: scope.openDecls } }

noncomputable def radialFlat
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : E) :
    Path p (intrinsicFramedExp (I := I) g hEnorm p u) where
  toFun t :=
    intrinsicFramedExp (I := I) g hEnorm p (flatTime t • u)
  continuous_toFun :=
    (intrinsicFrame_smooth (I := I) g hEnorm p).continuous.comp
      (by
        exact
          (flatTime_cd.continuous.comp continuous_subtype_val).smul
            continuous_const)
  source' := by
    change intrinsicFramedExp (I := I) g hEnorm p (flatTime (0 : Real) • u) = p
    rw [flatTime_zero, zero_smul, intrinsicFrame_zero]
  target' := by
    change
      intrinsicFramedExp (I := I) g hEnorm p (flatTime (1 : Real) • u) =
        intrinsicFramedExp (I := I) g hEnorm p u
    rw [flatTime_one, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat

private theorem radialFlat_extend_eq_radialPath
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : E) :
    (radialFlat g hEnorm p u).extend =
      (fun t : ℝ => (radialPath g p (normalFrame g p u) (by
        rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
        trivial)).withSittingInstants.extend t) := by
  have hco : (radialFlat g hEnorm p u : unitInterval → M) =
      (radialPath g p (normalFrame g p u) (by
        rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
        trivial)).withSittingInstants := by
    funext t
    change intrinsicFramedExp g hEnorm p (flatTime t • u) =
      (radialPath g p (normalFrame g p u) (by
        rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
        trivial)).withSittingInstants t
    rw [Path.withSittingInstants_apply, radialPath_apply]
    simp only [flatTime, intrinsicFrame_apply, map_smul, expMap_eq_expMapIntrinsic g hEnorm p]
  exact congrArg (_root_.Set.IccExtend zero_le_one) hco

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat_extend_eq_radialPath
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat_extend_eq_radialPath target :: scope.openDecls } }

theorem radialFlat_extend
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : E) :
    (radialFlat (I := I) g hEnorm p u).extend =
      fun t : Real =>
        intrinsicFramedExp (I := I) g hEnorm p (flatTime t • u) := by
  rw [radialFlat_extend_eq_radialPath, extend_radialPath_withSittingInstants]
  funext t
  simp only [flatTime, intrinsicFrame_apply, map_smul, expMap_eq_expMapIntrinsic g hEnorm p]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat_extend then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat_extend"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat_extend ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat_extend

theorem radialFlat_flat
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : E) :
    Path.IsContMDiffWithSittingInstants (I := I) 1 (radialFlat (I := I) g hEnorm p u) := by
  have hc := (radialPath g p (normalFrame g p u) (by
        rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
        trivial)).isContMDiffWithSittingInstants_withSittingInstants
    (contMDiffOn_extend_radialPath _ _ _ _)
  refine ⟨?_, ?_, ?_⟩
  · rw [radialFlat_extend_eq_radialPath]
    exact hc.contMDiff.of_le (by norm_num)
  · rw [radialFlat_extend_eq_radialPath]
    exact hc.eventuallyEq_zero
  · rw [radialFlat_extend_eq_radialPath]
    simpa only [intrinsicFrame_apply, ← expMap_eq_expMapIntrinsic g hEnorm p] using hc.eventuallyEq_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat_flat then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat_flat"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat_flat ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat_flat

theorem radialFlat_len
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : E) :
    Path.riemannianELength (I := I) (radialFlat (I := I) g hEnorm p u) =
      ENNReal.ofReal ‖u‖ := by
  rw [Path.riemannianELength, radialFlat_extend_eq_radialPath]
  change (radialPath g p (normalFrame g p u) (by
        rw [expDomain_eq_univ_of_completeSpace g hEnorm p]
        trivial)).withSittingInstants.riemannianELength (I := I) = ENNReal.ofReal ‖u‖
  rw [Path.riemannianELength_withSittingInstants _
      ((contMDiffOn_extend_radialPath _ _ _ _).mdifferentiableOn (by norm_num)),
    riemannianELength_radialPath g hEnorm, normalFrame_sqrt]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat_len then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat_len"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat_len ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlat_len

noncomputable def radialFlatLift
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : E) :
    IntrinsicFrameLift (I := I) g hEnorm p
      (radialFlat (I := I) g hEnorm p u).extend 0 1 where
  toFun t := flatTime t • u
  contDiff := by
    apply ContDiff.contDiffOn
    exact (flatTime_cd.of_le (by norm_num)).smul contDiff_const
  start := by rw [flatTime_zero, zero_smul]
  lifts := by
    intro t _
    rw [radialFlat_extend]
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlatLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlatLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlatLift ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialFlatLift

@[simp] theorem radialLift_one
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (w : TangentSpace I y),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y w w)))
    (p : M) (u : E) :
    (radialFlatLift (I := I) g hEnorm p u).toFun 1 = u := by
  change flatTime (1 : Real) • u = u
  rw [flatTime_one, one_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialLift_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialLift_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialLift_one ``Submission.DifferentialGeometry.Geometry.Riemannian.CheegerGromovTaylor.radialLift_one

end CheegerGromovTaylor
end Riemannian
end Geometry
end DifferentialGeometry
