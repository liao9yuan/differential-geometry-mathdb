import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientCylinderBranch
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderScalarNormalization
import Submission.DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Submission.Bundle
open _root_.Submission.DifferentialGeometry.Geometry
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Submission.ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => SphereTwo × ℝ
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "sphereMetric" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance coverScalarSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarSphereDimension target :: scope.openDecls } }
private local instance coverScalarSphereC1 : IsManifold (𝓡 2) 1 SphereTwo :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarSphereC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarSphereC1 target :: scope.openDecls } }
private local instance coverScalarCylinderC1 : IsManifold CylinderI 1 Cylinder :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarCylinderC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarCylinderC1 target :: scope.openDecls } }

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval}

private local instance coverScalarTopology : TopologicalSpace F.M := F.topology

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarTopology
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarTopology target :: scope.openDecls } }
private local instance coverScalarCharted : ChartedSpace H F.M := F.charted

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarCharted
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarCharted target :: scope.openDecls } }
private local instance coverScalarSmooth : IsManifold I ∞ F.M := F.smooth

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarSmooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarSmooth target :: scope.openDecls } }
private local instance coverScalarC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarC1
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarC1 target :: scope.openDecls } }
private local instance coverScalarT2 : T2Space F.M := F.t2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarT2
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarT2 target :: scope.openDecls } }
private local instance coverScalarSigmaCompact : SigmaCompactSpace F.M := F.sigmaCompact

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarSigmaCompact
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.coverScalarSigmaCompact target :: scope.openDecls } }

namespace ShrinkingCylinderCover

variable (C : ShrinkingCylinderCover F)

theorem metricScalarAt_eq_inv_sub (t : ℝ) (ht : t ≤ 0) (x : F.M) :
    metricScalarAt (I := I) (F.S.base.metric t) x = 1 / (C.extinctionTime - t) := by
  let gPull : SmoothRiemannianMetric CylinderI Cylinder :=
    localPullMetric (F.S.base.metric t) C.projection C.projection_local
  have hpositive : 0 < C.extinctionTime - t := by
    have hT := C.extinctionTime_pos
    linarith
  have hinner : ∀ (y : SphereTwo) (s : ℝ)
      (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
      gPull.inner (y, s) (v, a) (w, b) =
        (2 * (C.extinctionTime - t)) * (sphereMetric).inner y v w + a * b := by
    intro y s v w a b
    exact (localPullMetric_inner (F.S.base.metric t) C.projection C.projection_local
      (y, s) (v, a) (w, b)).trans (C.projection_metric t ht y s v w a b)
  obtain ⟨p, hp⟩ := C.surjective x
  change C.projection p = x at hp
  have hvalue := metricScalarAt_roundCylinder_of_inner_eq gPull
    (2 * (C.extinctionTime - t)) (mul_pos (by norm_num) hpositive) hinner p
  have hnatural := metricScalarAt_localPull (F.S.base.metric t)
    C.projection C.projection_local p
  have hscalar := hnatural.symm.trans hvalue
  rw [hp] at hscalar
  calc
    metricScalarAt (I := I) (F.S.base.metric t) x =
        2 / (2 * (C.extinctionTime - t)) := hscalar
    _ = 1 / (C.extinctionTime - t) := by
      rw [div_mul_eq_div_div]
      norm_num

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.metricScalarAt_eq_inv_sub then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.metricScalarAt_eq_inv_sub"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.metricScalarAt_eq_inv_sub ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.metricScalarAt_eq_inv_sub

theorem extinctionTime_eq_one_of_scalar_at_base_one
    (hbase : PointedFlowScalarAtBase F 1) : C.extinctionTime = 1 := by
  have hscalar : metricScalarAt (I := I) (F.S.base.metric 0) F.basepoint = 1 := by
    simpa only [PointedFlowScalarAtBase, SolutionOn.scalar, SolutionFamily.scalar]
      using hbase
  have hvalue := C.metricScalarAt_eq_inv_sub 0 le_rfl F.basepoint
  rw [hscalar, sub_zero] at hvalue
  have h := (eq_div_iff (ne_of_gt C.extinctionTime_pos)).mp hvalue
  simpa only [one_mul] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.extinctionTime_eq_one_of_scalar_at_base_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.extinctionTime_eq_one_of_scalar_at_base_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.extinctionTime_eq_one_of_scalar_at_base_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.extinctionTime_eq_one_of_scalar_at_base_one

include C in
theorem metricScalarAt_zero_eq_one_of_scalar_at_base_one
    (hbase : PointedFlowScalarAtBase F 1) (x : F.M) :
    metricScalarAt (I := I) (F.S.base.metric 0) x = 1 := by
  rw [C.metricScalarAt_eq_inv_sub 0 le_rfl x,
    C.extinctionTime_eq_one_of_scalar_at_base_one hbase, sub_zero, div_self one_ne_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.metricScalarAt_zero_eq_one_of_scalar_at_base_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.metricScalarAt_zero_eq_one_of_scalar_at_base_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.metricScalarAt_zero_eq_one_of_scalar_at_base_one ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.ShrinkingCylinderCover.metricScalarAt_zero_eq_one_of_scalar_at_base_one

end ShrinkingCylinderCover

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
