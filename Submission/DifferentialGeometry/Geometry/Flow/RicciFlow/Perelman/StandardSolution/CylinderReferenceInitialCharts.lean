import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.CylinderReferenceCopy
import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.GrowingInitialCylinderCharts
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Atlas
import Submission.DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import Submission.DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Basic
import Submission.DifferentialGeometry.Topology.Exhaustion

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false
noncomputable section
open _root_.Set _root_.Submission.Set _root_.Function _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Submission.Manifold _root_.TopologicalSpace _root_.Submission.DifferentialGeometry
open _root_.Submission.DifferentialGeometry.Geometry _root_.Submission.DifferentialGeometry.CheegerGromovCompactness
open _root_.Submission.DifferentialGeometry.Geometry.Metric _root_.Submission.DifferentialGeometry.Geometry.Neck _root_.Submission.DifferentialGeometry.PDE.RicciFlow.StandardCap
open scoped _root_.Manifold _root_.Submission.Manifold _root_.Submission.DifferentialGeometry.Manifold _root_.ContDiff _root_.Topology _root_.Submission.DifferentialGeometry.Geometry.Topology _root_.Submission.DifferentialGeometry.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.E3
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.E3 target :: scope.openDecls } }
private abbrev C := Metric.sphere (0 : E3) 1 × ℝ

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.C
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.C target :: scope.openDecls } }
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.IC
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.IC target :: scope.openDecls } }
private abbrev Q := cylinderReferenceCopy.Q

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.Q
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.Q target :: scope.openDecls } }
private local instance _root_.Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.instFactEqNatFinrankRealE3HAddOfNat target :: scope.openDecls } }

def cylinderReferenceOpenCylinder (L : ℝ) : _root_.TopologicalSpace.Opens Q :=
  ⟨cylinderReferenceCopy.equiv.symm ⁻¹' (openCylinder L : Set C),
    (openCylinder L).isOpen.preimage cylinderReferenceCopy.equiv.symm.continuous⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder

theorem cylinderReferenceOpenCylinder_eq_image (L : ℝ) :
    (cylinderReferenceOpenCylinder L : Set Q) =
      cylinderReferenceCopy.equiv '' (openCylinder L : Set C) := by
  ext q
  constructor
  · intro hq
    exact ⟨cylinderReferenceCopy.equiv.symm q, hq,
      cylinderReferenceCopy.equiv.apply_symm_apply q⟩
  · rintro ⟨p, hp, rfl⟩
    change cylinderReferenceCopy.equiv.symm (cylinderReferenceCopy.equiv p) ∈ openCylinder L
    rw [Diffeomorph.symm_apply_apply]
    exact hp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_eq_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_eq_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_eq_image ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_eq_image

theorem cylinderReferenceOpenCylinder_mono :
    Monotone (fun L : ℝ => (cylinderReferenceOpenCylinder L : Set Q)) := by
  intro L K hLK q hq
  change -K < (cylinderReferenceCopy.equiv.symm q).2 ∧
    (cylinderReferenceCopy.equiv.symm q).2 < K
  exact ⟨by linarith [hq.1], by linarith [hq.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_mono then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_mono"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_mono ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_mono

theorem cylinderReferenceOpenCylinder_exhausts :
    ExhaustsByOpen (fun k : ℕ =>
      (cylinderReferenceOpenCylinder ((k : ℝ) + 1) : Set Q)) where
  isOpen k := (cylinderReferenceOpenCylinder ((k : ℝ) + 1)).isOpen
  mono_step k := cylinderReferenceOpenCylinder_mono (by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith)
  subset := by
    intro K hK
    obtain ⟨L, _hL, hKL⟩ := compact_subset_openCylinder
      (hK.image cylinderReferenceCopy.equiv.symm.continuous)
    obtain ⟨k₀, hk₀⟩ := exists_nat_gt L
    refine ⟨k₀, ?_⟩
    intro k hk q hq
    have hp := hKL (_root_.Set.mem_image_of_mem cylinderReferenceCopy.equiv.symm hq)
    have hk' : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
    change -((k : ℝ) + 1) < (cylinderReferenceCopy.equiv.symm q).2 ∧
      (cylinderReferenceCopy.equiv.symm q).2 < (k : ℝ) + 1
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_exhausts then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_exhausts"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_exhausts ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_exhausts

theorem cylinderReferenceOpenCylinder_basepoint_mem {L : ℝ} (hL : 0 < L) :
    cylinderPointedReference.basepoint ∈ cylinderReferenceOpenCylinder L := by
  change cylinderReferenceCopy.equiv.symm
    (cylinderReferenceCopy.equiv (spherePoint, 0)) ∈ openCylinder L
  rw [cylinderReferenceCopy.equiv.symm_apply_apply]
  exact ⟨neg_neg_of_pos hL, hL⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_basepoint_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_basepoint_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_basepoint_mem ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceOpenCylinder_basepoint_mem

private theorem finiteCylinder_subset_polar_source (O : E3 ≃ₗᵢ[ℝ] E3)
    {a L : ℝ} (hfit : transitionEnd + L ≤ a) :
    (openCylinder L : Set C) ⊆ (initialPolarDiffeomorph O a).source := by
  intro p hp
  rw [initialPolarDiffeomorph_source]
  change 0 < a + p.2
  linarith [hp.1, transitionEnd_pos]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.finiteCylinder_subset_polar_source
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.finiteCylinder_subset_polar_source target :: scope.openDecls } }

private def finiteInitialPolar (O : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) : PartialDiffeomorph IC (𝓡 3) C E3 ∞ :=
  PartialDiffeomorph.ofOpenPartialHomeomorphRestr
    (initialPolarDiffeomorph O a).toOpenPartialHomeomorph
    (openCylinder L : Set C) (openCylinder L).isOpen
    (finiteCylinder_subset_polar_source O hfit)
    ((initialPolarDiffeomorph O a).contMDiffOn_toFun.mono
      (finiteCylinder_subset_polar_source O hfit))
    ((initialPolarDiffeomorph O a).contMDiffOn_invFun.mono (by
      rintro _ ⟨p, hp, rfl⟩
      exact (initialPolarDiffeomorph O a).map_source'
        (finiteCylinder_subset_polar_source O hfit hp)))

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.finiteInitialPolar
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.finiteInitialPolar target :: scope.openDecls } }

def cylinderReferenceInitialMap (O : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) : PartialDiffeomorph (𝓡 3) (𝓡 3) Q E3 ∞ :=
  cylinderReferenceCopy.equiv.symm.toPartialDiffeomorph.trans
    (finiteInitialPolar O a L hfit)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap

theorem cylinderReferenceInitialMap_apply (O : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) (q : Q) :
    cylinderReferenceInitialMap O a L hfit q =
      initialPolarDiffeomorph O a (cylinderReferenceCopy.equiv.symm q) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_apply

theorem cylinderReferenceInitialMap_symm_apply (O : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) (x : E3) :
    (cylinderReferenceInitialMap O a L hfit).symm x =
      cylinderReferenceCopy.equiv ((initialPolarDiffeomorph O a).symm x) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_symm_apply ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_symm_apply

theorem cylinderReferenceInitialMap_source (O : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) :
    (cylinderReferenceInitialMap O a L hfit).source =
      (cylinderReferenceOpenCylinder L : Set Q) := by
  ext q
  change (q ∈ (_root_.Set.univ : Set Q) ∧ cylinderReferenceCopy.equiv.symm q ∈ openCylinder L) ↔
    cylinderReferenceCopy.equiv.symm q ∈ openCylinder L
  simp only [_root_.Set.mem_univ, true_and]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_source ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_source

theorem cylinderReferenceInitialMap_target (O : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) :
    (cylinderReferenceInitialMap O a L hfit).target =
      (initialCylinderImage O a L hfit : Set E3) := by
  ext x
  change (x ∈ (initialCylinderImage O a L hfit : Set E3) ∧
    (initialPolarDiffeomorph O a).symm x ∈ (_root_.Set.univ : Set C)) ↔
      x ∈ (initialCylinderImage O a L hfit : Set E3)
  simp only [_root_.Set.mem_univ, and_true]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_target then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_target"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_target ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_target

theorem cylinderReferenceInitialMap_target_shell (O : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) :
    (cylinderReferenceInitialMap O a L hfit).target =
      {x : E3 | a - L < ‖x‖ ∧ ‖x‖ < a + L} := by
  rw [cylinderReferenceInitialMap_target, initialCylinderImage_eq_shell]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_target_shell then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_target_shell"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_target_shell ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_target_shell

private theorem cylinderReferenceInitialMap_mfderiv (O : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) (q : Q)
    (hq : q ∈ cylinderReferenceOpenCylinder L) (v : TangentSpace (𝓡 3) q) :
    mfderiv (𝓡 3) (𝓡 3) (cylinderReferenceInitialMap O a L hfit) q v =
      mfderiv IC (𝓡 3) (initialPolarDiffeomorph O a) (cylinderReferenceCopy.equiv.symm q)
        (mfderiv (𝓡 3) IC cylinderReferenceCopy.equiv.symm q v) := by
  change mfderiv (𝓡 3) (𝓡 3)
    (initialPolarDiffeomorph O a ∘ cylinderReferenceCopy.equiv.symm) q v = _
  rw [mfderiv_comp q
    ((initialPolarDiffeomorph O a).mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0)
      (finiteCylinder_subset_polar_source O hfit hq))
    (cylinderReferenceCopy.equiv.symm.contMDiff.mdifferentiableAt (by decide)),
    ContinuousLinearMap.comp_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_mfderiv
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_mfderiv target :: scope.openDecls } }

theorem cylinderReferenceInitialMap_metric_inner (O : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) (q : Q)
    (hq : q ∈ cylinderReferenceOpenCylinder L) (v w : TangentSpace (𝓡 3) q) :
    DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner (cylinderReferenceInitialMap O a L hfit q)
      (mfderiv (𝓡 3) (𝓡 3) (cylinderReferenceInitialMap O a L hfit) q v)
      (mfderiv (𝓡 3) (𝓡 3) (cylinderReferenceInitialMap O a L hfit) q w) =
        cylinderReferenceMetric.inner q v w := by
  let Ψ := cylinderReferenceInitialMap O a L hfit
  let p := cylinderReferenceCopy.equiv.symm q
  let dv := mfderiv (𝓡 3) IC cylinderReferenceCopy.equiv.symm q v
  let dw := mfderiv (𝓡 3) IC cylinderReferenceCopy.equiv.symm q w
  have hv := cylinderReferenceInitialMap_mfderiv O a L hfit q hq v
  have hw := cylinderReferenceInitialMap_mfderiv O a L hfit q hq w
  have htup :
      ((Ψ q : E3), (mfderiv (𝓡 3) (𝓡 3) Ψ q v : E3),
        (mfderiv (𝓡 3) (𝓡 3) Ψ q w : E3)) =
      ((initialPolarDiffeomorph O a p : E3),
        (mfderiv IC (𝓡 3) (initialPolarDiffeomorph O a) p dv : E3),
        (mfderiv IC (𝓡 3) (initialPolarDiffeomorph O a) p dw : E3)) :=
    Prod.ext (cylinderReferenceInitialMap_apply O a L hfit q) (Prod.ext hv hw)
  have hs := congrArg (fun z : E3 × E3 × E3 =>
    DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner z.1 z.2.1 z.2.2) htup
  have hi := initialPolarDiffeomorph_metric_inner O a p
    (by dsimp only [p]; linarith [hq.1]) dv dw
  exact hs.trans (hi.trans (cylinderReferenceMetric_inner q v w).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_metric_inner then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_metric_inner"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_metric_inner ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_metric_inner

theorem cylinderReferenceInitialMap_pullback (O : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) :
    let Ψ := cylinderReferenceInitialMap O a L hfit
    let U := cylinderReferenceOpenCylinder L
    let hU : (U : Set Q) ⊆ Ψ.source :=
      (cylinderReferenceInitialMap_source O a L hfit).symm.subset
    let V : _root_.TopologicalSpace.Opens E3 := ⟨Ψ '' (U : Set Q), image_opens_isOpen Ψ hU⟩
    Diffeomorph.pullbackMetric (DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.restrictOpen V)
      (PartialDiffeomorph.toOpensDiffeo Ψ hU) = cylinderReferenceMetric.restrictOpen U := by
  let Ψ := cylinderReferenceInitialMap O a L hfit
  let U : _root_.TopologicalSpace.Opens Q := cylinderReferenceOpenCylinder L
  have hU : (U : Set Q) ⊆ Ψ.source :=
    (cylinderReferenceInitialMap_source O a L hfit).symm.subset
  let V : _root_.TopologicalSpace.Opens E3 := ⟨Ψ '' (U : Set Q), image_opens_isOpen Ψ hU⟩
  let e : U ≃ₘ⟮𝓡 3, 𝓡 3⟯ V := PartialDiffeomorph.toOpensDiffeo Ψ hU
  have h : Diffeomorph.pullbackMetric (DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.restrictOpen V)
      e = cylinderReferenceMetric.restrictOpen U := by
    apply SmoothRiemannianMetric.ext_inner
    intro q v w
    have hv : (mfderiv (𝓡 3) (𝓡 3) e q v : E3) =
        mfderiv (𝓡 3) (𝓡 3) Ψ q.val v :=
      PartialDiffeomorph.mfderiv_toOpensDiffeo Ψ hU q v
    have hw : (mfderiv (𝓡 3) (𝓡 3) e q w : E3) =
        mfderiv (𝓡 3) (𝓡 3) Ψ q.val w :=
      PartialDiffeomorph.mfderiv_toOpensDiffeo Ψ hU q w
    have hs := congrArg₂ (fun u z : E3 =>
      DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.inner (Ψ q.val) u z) hv hw
    have hi := cylinderReferenceInitialMap_metric_inner O a L hfit q.val q.property v w
    have hp := Diffeomorph.pullbackMetric_inner
      (DifferentialGeometry.PDE.RicciFlow.StandardCap.metric.restrictOpen V) e q v w
    exact hp.trans (hs.trans hi)
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_pullback then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_pullback"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_pullback ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_pullback

theorem cylinderReferenceInitialMap_image (O : E3 ≃ₗᵢ[ℝ] E3) (a L : ℝ)
    (hfit : transitionEnd + L ≤ a) :
    cylinderReferenceInitialMap O a L hfit '' (cylinderReferenceOpenCylinder L : Set Q) =
      (initialCylinderImage O a L hfit : Set E3) := by
  rw [← cylinderReferenceInitialMap_source O a L hfit]
  exact (cylinderReferenceInitialMap O a L hfit).toPartialEquiv.image_source_eq_target.trans
    (cylinderReferenceInitialMap_target O a L hfit)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_image ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_image

theorem cylinderReferenceInitialMap_pointed_of_distance (x : E3) (L : ℝ) (hL : 0 < L)
    (hx : transitionEnd + L ≤
      (riemannianEDistOf DifferentialGeometry.PDE.RicciFlow.StandardCap.metric 0 x).toReal) :
    ∃ hfit : transitionEnd + L ≤ ‖x‖,
      cylinderPointedReference.basepoint ∈
        (cylinderReferenceInitialMap (pointedInitialRotation x) ‖x‖ L hfit).source ∧
      cylinderReferenceInitialMap (pointedInitialRotation x) ‖x‖ L hfit
        cylinderPointedReference.basepoint = x := by
  have hfit : transitionEnd + L ≤ ‖x‖ := by rwa [distance_zero] at hx
  refine ⟨hfit, ?_, ?_⟩
  · rw [cylinderReferenceInitialMap_source]
    exact cylinderReferenceOpenCylinder_basepoint_mem hL
  · change cylinderReferenceInitialMap (pointedInitialRotation x) ‖x‖ L hfit
      (cylinderReferenceCopy.equiv (spherePoint, 0)) = x
    rw [cylinderReferenceInitialMap_apply]
    change initialPolarDiffeomorph (pointedInitialRotation x) ‖x‖
      (cylinderReferenceCopy.equiv.symm (cylinderReferenceCopy.equiv (spherePoint, 0))) = x
    rw [cylinderReferenceCopy.equiv.symm_apply_apply]
    exact pointedInitialRotation_center x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_pointed_of_distance then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_pointed_of_distance"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_pointed_of_distance ``Submission.DifferentialGeometry.PDE.RicciFlow.cylinderReferenceInitialMap_pointed_of_distance

end DifferentialGeometry.PDE.RicciFlow

end
