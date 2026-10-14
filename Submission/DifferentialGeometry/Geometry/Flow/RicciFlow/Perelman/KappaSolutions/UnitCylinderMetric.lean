import Submission.DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open _root_.Bundle _root_.Manifold
open _root_.Submission.DifferentialGeometry.Geometry
open scoped _root_.Manifold _root_.ContDiff _root_.Topology


abbrev SpatialNeckSphere := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSphere then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSphere"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSphere ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckSphere


abbrev SpatialNeckCylinder := SpatialNeckSphere × ℝ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckCylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckCylinder


abbrev SpatialNeckCylinderModel := (𝓡 2).prod 𝓘(ℝ, ℝ)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckCylinderModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckCylinderModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckCylinderModel ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SpatialNeckCylinderModel

private local instance unitCylinderSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderSphereDimension
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderSphereDimension target :: scope.openDecls } }

private abbrev SphereModelSpace := EuclideanSpace ℝ (Fin 2)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereModelSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.SphereModelSpace target :: scope.openDecls } }
private abbrev CylinderModelSpace := SphereModelSpace × ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderModelSpace
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.CylinderModelSpace target :: scope.openDecls } }

private def unitCylinderInner (p : SpatialNeckCylinder) :
    TangentSpace SpatialNeckCylinderModel p →L[ℝ]
      TangentSpace SpatialNeckCylinderModel p →L[ℝ] ℝ :=
  ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1).bilinearComp
      (ContinuousLinearMap.fst ℝ SphereModelSpace ℝ)
      (ContinuousLinearMap.fst ℝ SphereModelSpace ℝ) +
    (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (ContinuousLinearMap.snd ℝ SphereModelSpace ℝ)
      (ContinuousLinearMap.snd ℝ SphereModelSpace ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderInner
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderInner target :: scope.openDecls } }

private theorem unitCylinderInner_apply (p : SpatialNeckCylinder)
    (V W : TangentSpace SpatialNeckCylinderModel p) :
    unitCylinderInner p V W =
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1 V.1 W.1 +
        V.2 * W.2 := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderInner_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderInner_apply target :: scope.openDecls } }

private theorem unitCylinderInner_pos (p : SpatialNeckCylinder)
    (V : TangentSpace SpatialNeckCylinderModel p) (hV : V ≠ 0) :
    0 < unitCylinderInner p V V := by
  rw [unitCylinderInner_apply]
  by_cases hhorizontal : V.1 = 0
  · have hvertical : V.2 ≠ 0 := by
      intro hv
      exact hV (Prod.ext hhorizontal hv)
    have hzero :
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1 V.1 V.1 = 0 := by
      exact (congrArg (fun v : TangentSpace (𝓡 2) p.1 =>
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1 v v)
        hhorizontal).trans
          (map_zero ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1 0))
    rw [hzero, zero_add]
    nlinarith [sq_pos_of_ne_zero hvertical]
  · have hround := (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).pos
      p.1 V.1 hhorizontal
    nlinarith [sq_nonneg V.2]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderInner_pos
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderInner_pos target :: scope.openDecls } }

private theorem unitCylinder_horizontal_section
    (Y : ContMDiffSection SpatialNeckCylinderModel CylinderModelSpace ∞
      (TangentSpace SpatialNeckCylinderModel : SpatialNeckCylinder → Type _)) :
    ContMDiff SpatialNeckCylinderModel ((𝓡 2).prod 𝓘(ℝ, SphereModelSpace)) ∞
      (fun p : SpatialNeckCylinder => TotalSpace.mk' SphereModelSpace
        (E := TangentSpace (𝓡 2)) p.1 (Y p).1) := by
  have hf : ContMDiff SpatialNeckCylinderModel (𝓡 2) ∞
      (Prod.fst : SpatialNeckCylinder → SpatialNeckSphere) := contMDiff_fst
  have ht : ContMDiff SpatialNeckCylinderModel ((𝓡 2).prod 𝓘(ℝ, SphereModelSpace)) ∞
      (fun p : SpatialNeckCylinder => TotalSpace.mk' SphereModelSpace
        (E := TangentSpace (𝓡 2)) p.1
        (mfderiv SpatialNeckCylinderModel (𝓡 2) Prod.fst p (Y p))) :=
    (hf.contMDiff_tangentMap (le_refl _)).comp Y.contMDiff
  have heq : (fun p : SpatialNeckCylinder => TotalSpace.mk' SphereModelSpace
      (E := TangentSpace (𝓡 2)) p.1
      (mfderiv SpatialNeckCylinderModel (𝓡 2) Prod.fst p (Y p))) =
      (fun p : SpatialNeckCylinder => TotalSpace.mk' SphereModelSpace
        (E := TangentSpace (𝓡 2)) p.1 (Y p).1) := by
    funext p
    rw [mfderiv_fst]
    rfl
  rw [heq] at ht
  exact ht

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinder_horizontal_section
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinder_horizontal_section target :: scope.openDecls } }

private theorem unitCylinder_vertical_section
    (Y : ContMDiffSection SpatialNeckCylinderModel CylinderModelSpace ∞
      (TangentSpace SpatialNeckCylinderModel : SpatialNeckCylinder → Type _)) :
    ContMDiff SpatialNeckCylinderModel 𝓘(ℝ, ℝ) ∞
      (fun p : SpatialNeckCylinder => (Y p).2) := by
  have hf : ContMDiff SpatialNeckCylinderModel 𝓘(ℝ, ℝ) ∞
      (Prod.snd : SpatialNeckCylinder → ℝ) := contMDiff_snd
  have ht' : ContMDiff SpatialNeckCylinderModel (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : SpatialNeckCylinder => TotalSpace.mk' ℝ
        (E := TangentSpace 𝓘(ℝ, ℝ)) p.2
        (mfderiv SpatialNeckCylinderModel 𝓘(ℝ, ℝ) Prod.snd p (Y p))) :=
    (hf.contMDiff_tangentMap (le_refl _)).comp Y.contMDiff
  have heq : (fun p : SpatialNeckCylinder => TotalSpace.mk' ℝ
      (E := TangentSpace 𝓘(ℝ, ℝ)) p.2
      (mfderiv SpatialNeckCylinderModel 𝓘(ℝ, ℝ) Prod.snd p (Y p))) =
      (fun p : SpatialNeckCylinder => TotalSpace.mk' ℝ
        (E := TangentSpace 𝓘(ℝ, ℝ)) p.2 (Y p).2) := by
    funext p
    rw [mfderiv_snd]
    rfl
  have ht : ContMDiff SpatialNeckCylinderModel (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : SpatialNeckCylinder => TotalSpace.mk' ℝ
        (E := TangentSpace 𝓘(ℝ, ℝ)) p.2 (Y p).2) := by
    rw [heq] at ht'
    exact ht'
  intro p
  have hp := ht p
  rw [_root_.Bundle.contMDiffAt_totalSpace] at hp
  simpa only [trivializationAt_model_space_apply] using hp.2

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinder_vertical_section
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinder_vertical_section target :: scope.openDecls } }

private theorem unitCylinder_evaluation_smooth
    (Y W : ContMDiffSection SpatialNeckCylinderModel CylinderModelSpace ∞
      (TangentSpace SpatialNeckCylinderModel : SpatialNeckCylinder → Type _)) :
    ContMDiff SpatialNeckCylinderModel 𝓘(ℝ, ℝ) ∞
      (fun p : SpatialNeckCylinder => unitCylinderInner p (Y p) (W p)) := by
  have hv := unitCylinder_horizontal_section Y
  have hw := unitCylinder_horizontal_section W
  have hg : ContMDiff SpatialNeckCylinderModel
      ((𝓡 2).prod 𝓘(ℝ, SphereModelSpace →L[ℝ] SphereModelSpace →L[ℝ] ℝ)) ∞
      (fun p : SpatialNeckCylinder => TotalSpace.mk'
        (SphereModelSpace →L[ℝ] SphereModelSpace →L[ℝ] ℝ)
        (E := fun y : SpatialNeckSphere =>
          TangentSpace (𝓡 2) y →L[ℝ] TangentSpace (𝓡 2) y →L[ℝ] ℝ)
        p.1 ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1)) :=
    (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).contMDiff.comp contMDiff_fst
  have htotal : ContMDiff SpatialNeckCylinderModel ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : SpatialNeckCylinder => TotalSpace.mk' ℝ
        (E := Bundle.Trivial SpatialNeckSphere ℝ) p.1
        ((roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1
          (Y p).1 (W p).1)) :=
    ContMDiff.clm_bundle_apply₂
      (E₁ := fun y : SpatialNeckSphere => TangentSpace (𝓡 2) y)
      (E₂ := fun y : SpatialNeckSphere => TangentSpace (𝓡 2) y)
      (E₃ := fun _ : SpatialNeckSphere => ℝ)
      (b := fun p : SpatialNeckCylinder => p.1)
      (ψ := fun p : SpatialNeckCylinder =>
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1)
      (v := fun p : SpatialNeckCylinder => (Y p).1)
      (w := fun p : SpatialNeckCylinder => (W p).1) hg hv hw
  have hround : ContMDiff SpatialNeckCylinderModel 𝓘(ℝ, ℝ) ∞
      (fun p : SpatialNeckCylinder =>
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1
          (Y p).1 (W p).1) := by
    intro p
    have hp := htotal p
    rw [_root_.Bundle.contMDiffAt_totalSpace] at hp
    exact hp.2
  have heq : (fun p : SpatialNeckCylinder => unitCylinderInner p (Y p) (W p)) =
      (fun p : SpatialNeckCylinder =>
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1
          (Y p).1 (W p).1) +
        (fun p : SpatialNeckCylinder => (Y p).2) * (fun p => (W p).2) := by
    funext p
    exact unitCylinderInner_apply p (Y p) (W p)
  rw [heq]
  exact hround.add ((unitCylinder_vertical_section Y).mul (unitCylinder_vertical_section W))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinder_evaluation_smooth
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinder_evaluation_smooth target :: scope.openDecls } }

def unitCylinderMetric :
    SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder where
  inner := unitCylinderInner
  symm p V W := by
    rw [unitCylinderInner_apply, unitCylinderInner_apply,
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).symm p.1 V.1 W.1,
      mul_comm V.2 W.2]
  pos := unitCylinderInner_pos
  isVonNBounded p := posDef_isVonNBounded (E := CylinderModelSpace) (unitCylinderInner p)
    (fun V hV => unitCylinderInner_pos p V hV)
  contMDiff := by
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun p : SpatialNeckCylinder =>
        TangentSpace SpatialNeckCylinderModel p →L[ℝ] ℝ)
      (φ := unitCylinderInner)
    intro Y
    apply contMDiff_continuousLinearMap_section_of_apply
      (V₂ := fun _ : SpatialNeckCylinder => ℝ)
      (φ := fun p => unitCylinderInner p (Y p))
    intro W p
    rw [_root_.Bundle.contMDiffAt_section]
    refine ((unitCylinder_evaluation_smooth Y W) p).congr_of_eventuallyEq ?_
    filter_upwards with q
    rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderMetric then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderMetric"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderMetric ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderMetric

theorem unitCylinderMetric_inner (y : SpatialNeckSphere) (z : ℝ)
    (v w : TangentSpace (𝓡 2) y) (a b : ℝ) :
    unitCylinderMetric.inner (y, z) (v, a) (w, b) =
      (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w + a * b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderMetric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderMetric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderMetric_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderMetric_inner

theorem unitCylinderMetric_unique
    (g : SmoothRiemannianMetric SpatialNeckCylinderModel SpatialNeckCylinder)
    (hinner : ∀ (y : SpatialNeckSphere) (z : ℝ)
      (v w : TangentSpace (𝓡 2) y) (a b : ℝ),
      g.inner (y, z) (v, a) (w, b) =
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner y v w + a * b) :
    g = unitCylinderMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro p V W
  exact hinner p.1 p.2 V.1 W.1 V.2 W.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderMetric_unique then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderMetric_unique"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderMetric_unique ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.unitCylinderMetric_unique

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
