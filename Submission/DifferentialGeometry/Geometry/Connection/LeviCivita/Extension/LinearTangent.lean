import Submission.DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Defs
import Submission.DifferentialGeometry.Geometry.Connection.ChartFrame.RicciIdentitySmoothFrame
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.Defs
import Submission.DifferentialGeometry.Geometry.Connection.LeviCivita.Christoffel.CorrectionAtBasepoint
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Analysis.Calculus.FDeriv.Congr

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.FiberBundle _root_.NormedSpace
open scoped _root_.Manifold _root_.Topology _root_.ContDiff


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open _root_.Submission.DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def tangentCoord (x : M) (w : TangentSpace I x) : E :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentCoord then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentCoord"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentCoord ``Submission.DifferentialGeometry.Geometry.Connection.tangentCoord

omit [FiniteDimensional ℝ E] in
@[simp] lemma tangentCoord_apply (x : M) (w : TangentSpace I x) :
    tangentCoord (I := I) x w =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x w := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentCoord_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentCoord_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentCoord_apply ``Submission.DifferentialGeometry.Geometry.Connection.tangentCoord_apply

omit [FiniteDimensional ℝ E] in
lemma tangentCoord_zero (x : M) : tangentCoord (I := I) x 0 = 0 := by
  simp [tangentCoord]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentCoord_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentCoord_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentCoord_zero ``Submission.DifferentialGeometry.Geometry.Connection.tangentCoord_zero

omit [FiniteDimensional ℝ E] in
lemma tangentCoord_smul (x : M) (c : ℝ) (w : TangentSpace I x) :
    tangentCoord (I := I) x (c • w) = c • tangentCoord (I := I) x w := by
  simp [tangentCoord]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.tangentCoord_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.tangentCoord_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.tangentCoord_smul ``Submission.DifferentialGeometry.Geometry.Connection.tangentCoord_smul

def coordExtensionTangent (x : M) (w : TangentSpace I x) (b : M) : TangentSpace I b :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).symmL ℝ b (tangentCoord (I := I) x w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.coordExtensionTangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.coordExtensionTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.coordExtensionTangent ``Submission.DifferentialGeometry.Geometry.Connection.coordExtensionTangent

omit [FiniteDimensional ℝ E] in
@[simp] lemma coordExtensionTangent_apply (x : M) (w : TangentSpace I x) (b : M) :
    coordExtensionTangent (I := I) x w b =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).symmL ℝ b (tangentCoord (I := I) x w) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.coordExtensionTangent_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.coordExtensionTangent_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.coordExtensionTangent_apply ``Submission.DifferentialGeometry.Geometry.Connection.coordExtensionTangent_apply

omit [FiniteDimensional ℝ E] in
lemma coordExtensionTangent_self (x : M) (w : TangentSpace I x) :
    coordExtensionTangent (I := I) x w x = w := by
  classical
  have hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' x
  simp only [coordExtensionTangent_apply, tangentCoord_apply]
  exact (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).symmL_continuousLinearMapAt hx w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.coordExtensionTangent_self then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.coordExtensionTangent_self"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.coordExtensionTangent_self ``Submission.DifferentialGeometry.Geometry.Connection.coordExtensionTangent_self

omit [FiniteDimensional ℝ E] in
lemma coordExtensionTangent_map_zero (x : M) (b : M) :
    coordExtensionTangent (I := I) x (0 : TangentSpace I x) b = 0 := by
  rw [coordExtensionTangent_apply, tangentCoord_zero, map_zero]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.coordExtensionTangent_map_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.coordExtensionTangent_map_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.coordExtensionTangent_map_zero ``Submission.DifferentialGeometry.Geometry.Connection.coordExtensionTangent_map_zero

omit [FiniteDimensional ℝ E] in
lemma coordExtensionTangent_map_smul (x : M) (c : ℝ) (w : TangentSpace I x) (b : M) :
    coordExtensionTangent (I := I) x (c • w) b =
      c • coordExtensionTangent (I := I) x w b := by
  simp only [coordExtensionTangent_apply, tangentCoord_smul, map_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.coordExtensionTangent_map_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.coordExtensionTangent_map_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.coordExtensionTangent_map_smul ``Submission.DifferentialGeometry.Geometry.Connection.coordExtensionTangent_map_smul

omit [FiniteDimensional ℝ E] in
lemma coordExtensionTangent_contMDiffOn (x : M) (w : TangentSpace I x) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (coordExtensionTangent (I := I) x w))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet := by
  classical
  have hiff :=
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞)
      (s := fun b => coordExtensionTangent (I := I) x w b)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => tangentCoord (I := I) x w)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro b hb
  change (_root_.FiberBundle.trivializationAt E (TangentSpace I) x
      ⟨b, coordExtensionTangent (I := I) x w b⟩).2 = tangentCoord (I := I) x w
  have happ :
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x
        ⟨b, (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).symm b
          (tangentCoord (I := I) x w)⟩).2
        = tangentCoord (I := I) x w := by
    have h := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).apply_mk_symm hb
      (tangentCoord (I := I) x w)
    simpa using congrArg Prod.snd h
  rw [coordExtensionTangent, Trivialization.symmL_apply _ hb]
  exact happ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.coordExtensionTangent_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.coordExtensionTangent_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.coordExtensionTangent_contMDiffOn ``Submission.DifferentialGeometry.Geometry.Connection.coordExtensionTangent_contMDiffOn

def linExtBump (x : M) : SmoothBumpFunction I x :=
  Classical.arbitrary (SmoothBumpFunction I x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.linExtBump then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.linExtBump"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.linExtBump ``Submission.DifferentialGeometry.Geometry.Connection.linExtBump

def linearExtensionTangent (x : M) (w : TangentSpace I x) :
    Π b : M, TangentSpace I b :=
  fun b => (linExtBump (I := I) x : M → ℝ) b • coordExtensionTangent (I := I) x w b

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.linearExtensionTangent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.linearExtensionTangent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.linearExtensionTangent ``Submission.DifferentialGeometry.Geometry.Connection.linearExtensionTangent

@[simp] lemma linearExtensionTangent_apply (x : M) (w : TangentSpace I x) (b : M) :
    linearExtensionTangent (I := I) x w b =
      (linExtBump (I := I) x : M → ℝ) b • coordExtensionTangent (I := I) x w b := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.linearExtensionTangent_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.linearExtensionTangent_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.linearExtensionTangent_apply ``Submission.DifferentialGeometry.Geometry.Connection.linearExtensionTangent_apply

omit [IsManifold I ∞ M] in
lemma linExtBump_eq_one (x : M) : (linExtBump (I := I) x : M → ℝ) x = 1 :=
  (linExtBump (I := I) x).eq_one

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.linExtBump_eq_one then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.linExtBump_eq_one"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.linExtBump_eq_one ``Submission.DifferentialGeometry.Geometry.Connection.linExtBump_eq_one

theorem linearExtensionTangent_eq (x : M) (w : TangentSpace I x) :
    linearExtensionTangent (I := I) x w x = w := by
  rw [linearExtensionTangent_apply, linExtBump_eq_one, one_smul,
    coordExtensionTangent_self]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.linearExtensionTangent_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.linearExtensionTangent_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.linearExtensionTangent_eq ``Submission.DifferentialGeometry.Geometry.Connection.linearExtensionTangent_eq

theorem linearExtensionTangent_map_zero (x : M) :
    linearExtensionTangent (I := I) x (0 : TangentSpace I x) = 0 := by
  funext b
  rw [linearExtensionTangent_apply, coordExtensionTangent_map_zero, smul_zero]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.linearExtensionTangent_map_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.linearExtensionTangent_map_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.linearExtensionTangent_map_zero ``Submission.DifferentialGeometry.Geometry.Connection.linearExtensionTangent_map_zero

theorem linearExtensionTangent_map_smul (x : M) (c : ℝ) (w : TangentSpace I x) :
    linearExtensionTangent (I := I) x (c • w) =
      c • linearExtensionTangent (I := I) x w := by
  funext b
  rw [Pi.smul_apply, linearExtensionTangent_apply, linearExtensionTangent_apply,
    coordExtensionTangent_map_smul, _root_.SMulCommClass.smul_comm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.linearExtensionTangent_map_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.linearExtensionTangent_map_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.linearExtensionTangent_map_smul ``Submission.DifferentialGeometry.Geometry.Connection.linearExtensionTangent_map_smul

theorem linearExtensionTangent_smooth [T2Space M] (x : M) (w : TangentSpace I x) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (linearExtensionTangent (I := I) x w)) := by
  classical
  set u : Set M := (chartAt H x).source with hu_def
  set ψ : M → ℝ := (linExtBump (I := I) x : M → ℝ) with hψ_def
  have hψ_smooth : ContMDiffOn I 𝓘(ℝ) ∞ ψ u :=
    (linExtBump (I := I) x).contMDiff.contMDiffOn
  have hu_open : IsOpen u := (chartAt H x).open_source
  have hψ_tsupport : tsupport ψ ⊆ u :=
    (linExtBump (I := I) x).tsupport_subset_chartAt_source
  have hs_smooth : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (T% (fun b : M => coordExtensionTangent (I := I) x w b)) u := by
    rw [show u = (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet from rfl]
    exact coordExtensionTangent_contMDiffOn (I := I) x w
  have h := ContMDiffOn.smul_section_of_tsupport (𝕜 := ℝ) (n := ∞)
    (V := TangentSpace I) hψ_smooth hu_open hψ_tsupport hs_smooth
  have h_eq : (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
        (linearExtensionTangent (I := I) x w b)) =
      (fun b : M => TotalSpace.mk' E (E := TangentSpace I) b
        ((ψ • fun b' : M => coordExtensionTangent (I := I) x w b') b)) := by
    funext b
    change TotalSpace.mk' E b (linearExtensionTangent (I := I) x w b) =
      TotalSpace.mk' E b ((ψ b) • coordExtensionTangent (I := I) x w b)
    rw [linearExtensionTangent_apply]
  rw [h_eq]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.linearExtensionTangent_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.linearExtensionTangent_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.linearExtensionTangent_smooth ``Submission.DifferentialGeometry.Geometry.Connection.linearExtensionTangent_smooth

section Reduction

variable [NeZero (Module.finrank ℝ E)]
  [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M] in
lemma chartE_section_repr_coordExtensionTangent_eq
    (x : M) (w : TangentSpace I x) {b : M}
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet) :
    chartESectionRepr (I := I) x (coordExtensionTangent (I := I) x w) b =
      tangentCoord (I := I) x w := by
  rw [chartE_section_repr_eq_trivToE, coordExtensionTangent_apply]
  exact (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).continuousLinearMapAt_symmL (R := ℝ) hb _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartE_section_repr_coordExtensionTangent_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartE_section_repr_coordExtensionTangent_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartE_section_repr_coordExtensionTangent_eq ``Submission.DifferentialGeometry.Geometry.Connection.chartE_section_repr_coordExtensionTangent_eq

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
lemma chartE_section_repr_linearExtensionTangent_eventuallyEq_const
    (x : M) (w : TangentSpace I x) :
    chartESectionRepr (I := I) x (linearExtensionTangent (I := I) x w)
      =ᶠ[𝓝 x] (fun _ : M => tangentCoord (I := I) x w) := by
  classical
  have h1 : {b : M | (linExtBump (I := I) x : M → ℝ) b = 1} ∈ 𝓝 x :=
    (linExtBump (I := I) x).eventuallyEq_one
  have h2 : (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet ∈ 𝓝 x := by
    rw [show (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).baseSet = (chartAt H x).source from rfl]
    exact (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  filter_upwards [h1, h2] with b hb1 hb2
  have hWb : linearExtensionTangent (I := I) x w b =
      coordExtensionTangent (I := I) x w b := by
    rw [linearExtensionTangent_apply, hb1, one_smul]
  change chartESectionRepr (I := I) x (linearExtensionTangent (I := I) x w) b =
    tangentCoord (I := I) x w
  rw [chartE_section_repr_eq_trivToE, hWb, ← chartE_section_repr_eq_trivToE]
  exact chartE_section_repr_coordExtensionTangent_eq (I := I) x w hb2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartE_section_repr_linearExtensionTangent_eventuallyEq_const then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartE_section_repr_linearExtensionTangent_eventuallyEq_const"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartE_section_repr_linearExtensionTangent_eventuallyEq_const ``Submission.DifferentialGeometry.Geometry.Connection.chartE_section_repr_linearExtensionTangent_eventuallyEq_const

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
    [BoundarylessManifold I M] in
lemma fderiv_chartE_section_repr_linearExtensionTangent_eq_zero
    (x : M) (w : TangentSpace I x) :
    fderiv ℝ (chartESectionRepr (I := I) x (linearExtensionTangent (I := I) x w)
        ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 := by
  classical
  have hconst :
      (chartESectionRepr (I := I) x (linearExtensionTangent (I := I) x w)
          ∘ (extChartAt I x).symm)
        =ᶠ[𝓝 (extChartAt I x x)] (fun _ : E => tangentCoord (I := I) x w) := by
    have hsymm_cont : ContinuousAt (extChartAt I x).symm (extChartAt I x x) :=
      continuousAt_extChartAt_symm x
    have hsymm_pt : (extChartAt I x).symm (extChartAt I x x) = x :=
      extChartAt_to_inv x
    have hmem : {b : M | chartESectionRepr (I := I) x
          (linearExtensionTangent (I := I) x w) b = tangentCoord (I := I) x w}
        ∈ 𝓝 ((extChartAt I x).symm (extChartAt I x x)) := by
      rw [hsymm_pt]
      exact chartE_section_repr_linearExtensionTangent_eventuallyEq_const (I := I) x w
    have hpre :
        (extChartAt I x).symm ⁻¹'
          {b : M | chartESectionRepr (I := I) x (linearExtensionTangent (I := I) x w) b
            = tangentCoord (I := I) x w}
          ∈ 𝓝 (extChartAt I x x) :=
      hsymm_cont.preimage_mem_nhds hmem
    filter_upwards [hpre] with y hy
    exact hy
  rw [hconst.fderiv_eq]
  exact fderiv_const_apply (𝕜 := ℝ) (tangentCoord (I := I) x w)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.fderiv_chartE_section_repr_linearExtensionTangent_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.fderiv_chartE_section_repr_linearExtensionTangent_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.fderiv_chartE_section_repr_linearExtensionTangent_eq_zero ``Submission.DifferentialGeometry.Geometry.Connection.fderiv_chartE_section_repr_linearExtensionTangent_eq_zero

omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
theorem covApply_linearExtensionTangent_basepoint_eq
    (g : SmoothRiemannianMetric I M) (x : M) (w : TangentSpace I x)
    (v : TangentSpace I x) :
    (LeviCivita (I := I) g).toFun (linearExtensionTangent (I := I) x w) x v =
      trivFromE (I := I) x x
        (christoffelCorrection (I := I) g x x (tangentCoord (I := I) x w) v) := by
  classical
  have hself : x ∈ chartLeviCivitaGoodSet (I := I) x :=
    self_mem_chartLeviCivitaGoodSet (I := I) (α := x)
  have hMDiff : MDiffAt (T% (linearExtensionTangent (I := I) x w)) x :=
    (linearExtensionTangent_smooth (I := I) x w).mdifferentiableAt (by norm_num)
  rw [LeviCivita_chart_apply (I := I) g x hself hMDiff v]
  rw [chartLeviCivita_apply (I := I) g x (linearExtensionTangent (I := I) x w) hself v]
  rw [fderiv_chartE_section_repr_linearExtensionTangent_eq_zero (I := I) x w]
  have hreprx : chartESectionRepr (I := I) x (linearExtensionTangent (I := I) x w) x =
      tangentCoord (I := I) x w := by
    rw [chartE_section_repr_eq_trivToE, linearExtensionTangent_eq]
    rfl
  rw [hreprx]
  simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.covApply_linearExtensionTangent_basepoint_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.covApply_linearExtensionTangent_basepoint_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.covApply_linearExtensionTangent_basepoint_eq ``Submission.DifferentialGeometry.Geometry.Connection.covApply_linearExtensionTangent_basepoint_eq

end Reduction

end Connection
end Geometry
end DifferentialGeometry
