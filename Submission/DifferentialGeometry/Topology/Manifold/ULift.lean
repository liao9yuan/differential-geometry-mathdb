import Submission.DifferentialGeometry.Topology.Manifold.ClosedOriented
import Mathlib.Topology.Connected.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

namespace DifferentialGeometry.Topology

universe u v uE uH

@[implicit_reducible]
def uliftChartedSpace (H : Type uH) [TopologicalSpace H]
    (M : Type u) [TopologicalSpace M] [ChartedSpace H M] :
    ChartedSpace H (ULift.{v} M) :=
  let h : ULift.{v} M ≃ₜ M := Homeomorph.ulift
  letI : ChartedSpace M (ULift.{v} M) :=
    h.toOpenPartialHomeomorph.singletonChartedSpace (by simp [h])
  ChartedSpace.comp H M (ULift.{v} M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.uliftChartedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.uliftChartedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.uliftChartedSpace ``Submission.DifferentialGeometry.Topology.uliftChartedSpace

attribute [local instance] uliftChartedSpace

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type u) [TopologicalSpace M] [ChartedSpace H M]

theorem isManifold_ulift [IsManifold I ∞ M] : IsManifold I ∞ (ULift.{v} M) := by
  let h : ULift.{v} M ≃ₜ M := Homeomorph.ulift
  let : ChartedSpace M (ULift.{v} M) :=
    h.toOpenPartialHomeomorph.singletonChartedSpace (by simp [h])
  let : ChartedSpace H (ULift.{v} M) := uliftChartedSpace H M
  let : HasGroupoid (ULift.{v} M) (@idRestrGroupoid M _) :=
    h.toOpenPartialHomeomorph.singleton_hasGroupoid (by simp [h]) (@idRestrGroupoid M _)
  let : HasGroupoid (ULift.{v} M) (contDiffGroupoid ∞ I) :=
    StructureGroupoid.HasGroupoid.comp (G₂ := @idRestrGroupoid M _) (by
      intro f hf
      have hsmooth {a : OpenPartialHomeomorph M M}
          (ha : a ∈ @idRestrGroupoid M _) : ContMDiffOn I I ∞ a a.source := by
        rcases ha with ⟨s, hs, ha⟩
        refine contMDiffOn_id.congr ?_
        intro x hx
        have hx' := OpenPartialHomeomorph.EqOnSource.eqOn ha hx
        simpa using hx'
      rw [isLocalStructomorphOn_contDiffGroupoid_iff]
      exact ⟨hsmooth hf, by
        simpa only [mfld_simps] using hsmooth ((@idRestrGroupoid M _).symm hf)⟩)
  exact IsManifold.mk' I ∞ (ULift.{v} M)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.isManifold_ulift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.isManifold_ulift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.isManifold_ulift ``Submission.DifferentialGeometry.Topology.isManifold_ulift

attribute [local instance] isManifold_ulift

def uliftDiffeomorph : M ≃ₘ⟮I, I⟯ ULift.{v} M := by
  let h : ULift.{v} M ≃ₜ M := Homeomorph.ulift
  refine
    { toEquiv := h.toEquiv.symm
      contMDiff_toFun := fun x => ?_
      contMDiff_invFun := fun x => ?_ }
  · refine contMDiffWithinAt_iff'.2 ⟨h.symm.continuous.continuousWithinAt, ?_⟩
    refine contDiff_id.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [Function.comp_apply]
      change extChartAt I x ((extChartAt I x).symm y) = y
      rw [(extChartAt I x).right_inv hy.1]
    · simp
  · refine contMDiffWithinAt_iff'.2 ⟨h.continuous.continuousWithinAt, ?_⟩
    refine contDiff_id.contDiffWithinAt.congr_of_mem (fun y hy => ?_) ?_
    · simp only [Function.comp_apply]
      change extChartAt I x ((extChartAt I x).symm y) = y
      rw [(extChartAt I x).right_inv hy.1]
    · simp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.uliftDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.uliftDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.uliftDiffeomorph ``Submission.DifferentialGeometry.Topology.uliftDiffeomorph

@[simp]
theorem uliftDiffeomorph_apply (x : M) : uliftDiffeomorph I M x = ULift.up x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.uliftDiffeomorph_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.uliftDiffeomorph_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.uliftDiffeomorph_apply ``Submission.DifferentialGeometry.Topology.uliftDiffeomorph_apply

@[simp]
theorem uliftDiffeomorph_symm_apply (x : ULift.{v} M) :
    (uliftDiffeomorph I M).symm x = x.down := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.uliftDiffeomorph_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.uliftDiffeomorph_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.uliftDiffeomorph_symm_apply ``Submission.DifferentialGeometry.Topology.uliftDiffeomorph_symm_apply

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] {n : ℕ}

omit [FiniteDimensional ℝ E] in
theorem chartAt_ulift (x : M) :
    chartAt H (ULift.up x : ULift.{v} M) =
      Homeomorph.ulift.toOpenPartialHomeomorph ≫ₕ chartAt H x := by
  let : ChartedSpace M (ULift.{v} M) :=
    Homeomorph.ulift.toOpenPartialHomeomorph.singletonChartedSpace (by simp)
  let : ChartedSpace H (ULift.{v} M) := uliftChartedSpace H M
  change @chartAt H _ (ULift.{v} M) _ (ChartedSpace.comp H M (ULift.{v} M))
    (ULift.up x) = _
  rw [chartAt_comp H M (ULift.up x : ULift.{v} M),
    OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.chartAt_ulift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.chartAt_ulift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.chartAt_ulift ``Submission.DifferentialGeometry.Topology.chartAt_ulift

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem extChartAt_ulift (x y : M) :
    extChartAt I (ULift.up x : ULift.{v} M) (ULift.up y) = extChartAt I x y := by
  rw [extChartAt_coe, extChartAt_coe]
  simp only [Function.comp_apply]
  rw [chartAt_ulift M x]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.extChartAt_ulift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.extChartAt_ulift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.extChartAt_ulift ``Submission.DifferentialGeometry.Topology.extChartAt_ulift

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem hasMFDerivAt_ulift_up (x : M) :
    HasMFDerivAt I I (ULift.up : M → ULift.{v} M) x (ContinuousLinearMap.id ℝ E) := by
  constructor
  · exact continuous_uliftUp.continuousAt
  · apply HasFDerivWithinAt.congr_of_eventuallyEq (hasFDerivWithinAt_id _ _)
    · apply Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin (I := I) x)
      intro y hy
      simp only [writtenInExtChartAt, Function.comp_apply, id_eq]
      rw [extChartAt_ulift I M x ((extChartAt I x).symm y)]
      exact (extChartAt I x).right_inv hy
    · simp only [writtenInExtChartAt, Function.comp_apply, id_eq]
      rw [(extChartAt I x).left_inv (mem_extChartAt_source x), extChartAt_ulift I M x x]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.hasMFDerivAt_ulift_up then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.hasMFDerivAt_ulift_up"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.hasMFDerivAt_ulift_up ``Submission.DifferentialGeometry.Topology.hasMFDerivAt_ulift_up

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mfderiv_ulift_up (x : M) :
    mfderiv I I (ULift.up : M → ULift.{v} M) x = ContinuousLinearMap.id ℝ E :=
  (hasMFDerivAt_ulift_up I M x).mfderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mfderiv_ulift_up then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mfderiv_ulift_up"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mfderiv_ulift_up ``Submission.DifferentialGeometry.Topology.mfderiv_ulift_up

omit [FiniteDimensional ℝ E] in
theorem mem_trivializationAt_baseSet_ulift (p x : M) :
    (ULift.up x : ULift.{v} M) ∈
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) (ULift.up p)).baseSet ↔
      x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet, TangentBundle.trivializationAt_baseSet,
    chartAt_ulift M p]
  rw [OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]
  simp only [Set.mem_inter_iff, Set.mem_univ, true_and, Set.mem_preimage]
  exact Iff.rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mem_trivializationAt_baseSet_ulift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mem_trivializationAt_baseSet_ulift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mem_trivializationAt_baseSet_ulift ``Submission.DifferentialGeometry.Topology.mem_trivializationAt_baseSet_ulift

omit [FiniteDimensional ℝ E] in
theorem tangentChartEquiv_ulift (p x : M)
    (hx : (ULift.up x : ULift.{v} M) ∈
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) (ULift.up p)).baseSet)
    (hxM : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet) :
    tangentChartEquiv I (ULift.{v} M) (ULift.up p) (ULift.up x) hx =
      tangentChartEquiv I M p x hxM := by
  have hu : (ULift.up x : ULift.{v} M) ∈ (chartAt H (ULift.up p)).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hx
  have hm : x ∈ (chartAt H p).source := by
    simpa only [TangentBundle.trivializationAt_baseSet] using hxM
  have hd : mfderiv I 𝓘(ℝ, E) (extChartAt I (ULift.up p)) (ULift.up x) =
      mfderiv I 𝓘(ℝ, E) (extChartAt I p) x := by
    have hcomp := mfderiv_comp (x := x) (I := I) (I' := I) (I'' := 𝓘(ℝ, E))
      (f := (ULift.up : M → ULift.{v} M))
      (g := (extChartAt I (ULift.up p) : ULift.{v} M → E))
      (mdifferentiableAt_extChartAt (I := I) (x := (ULift.up p : ULift.{v} M)) hu)
      (hasMFDerivAt_ulift_up I M x).mdifferentiableAt
    have heq : mfderiv I 𝓘(ℝ, E)
        ((extChartAt I (ULift.up p)) ∘ (ULift.up : M → ULift.{v} M)) x =
        mfderiv I 𝓘(ℝ, E) (extChartAt I p) x := by
      have hfun : ((extChartAt I (ULift.up p)) ∘ (ULift.up : M → ULift.{v} M)) =
          (extChartAt I p : M → E) :=
        funext fun z => extChartAt_ulift I M p z
      rw [hfun]
    rw [heq, mfderiv_ulift_up I M x] at hcomp
    rw [← hcomp.symm]
    exact ContinuousLinearMap.comp_id _
  have hc : (_root_.FiberBundle.trivializationAt E (TangentSpace I) (ULift.up p)).continuousLinearMapAt ℝ
        (ULift.up x) =
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ x := by
    rw [TangentBundle.continuousLinearMapAt_trivializationAt hu,
      TangentBundle.continuousLinearMapAt_trivializationAt hm]
    exact hd
  apply LinearEquiv.ext
  intro w
  calc
    tangentChartEquiv I (ULift.{v} M) (ULift.up p) (ULift.up x) hx w =
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) (ULift.up p)).continuousLinearMapAt ℝ
          (ULift.up x) w :=
      (Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) (ULift.up p)) hx w).symm
    _ = (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).continuousLinearMapAt ℝ x w :=
      congrArg (fun A : E →L[ℝ] E => A w) hc
    _ = tangentChartEquiv I M p x hxM w :=
      Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) p) hxM w

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.tangentChartEquiv_ulift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.tangentChartEquiv_ulift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.tangentChartEquiv_ulift ``Submission.DifferentialGeometry.Topology.tangentChartEquiv_ulift

def uliftTangentOrientation (o : ManifoldOrientation I M n) (x : ULift.{v} M) :
    Orientation ℝ (TangentSpace I x) (Fin n) :=
  Orientation.map (Fin n)
    ((uliftDiffeomorph I M).mfderivToContinuousLinearEquiv (by simp) x.down).toLinearEquiv
    (o.orientation x.down)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.uliftTangentOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.uliftTangentOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.uliftTangentOrientation ``Submission.DifferentialGeometry.Topology.uliftTangentOrientation

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem mfderivToContinuousLinearEquiv_ulift (y : ULift.{v} M) :
    ((uliftDiffeomorph I M).mfderivToContinuousLinearEquiv (by simp) y.down).toLinearEquiv =
      LinearEquiv.refl ℝ (TangentSpace I y) := by
  ext v
  change mfderiv I I (ULift.up : M → ULift.{v} M) y.down v = v
  rw [mfderiv_ulift_up I M y.down]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.mfderivToContinuousLinearEquiv_ulift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.mfderivToContinuousLinearEquiv_ulift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.mfderivToContinuousLinearEquiv_ulift ``Submission.DifferentialGeometry.Topology.mfderivToContinuousLinearEquiv_ulift

@[simp]
theorem uliftTangentOrientation_apply (o : ManifoldOrientation I M n) (x : M) :
    uliftTangentOrientation I M o (ULift.up x) = o.orientation x := by
  rw [uliftTangentOrientation]
  erw [mfderivToContinuousLinearEquiv_ulift I M (ULift.up x)]
  change Orientation.map (Fin n) (LinearEquiv.refl ℝ (TangentSpace I x)) (o.orientation x) =
    o.orientation x
  rw [Orientation.map_refl]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.uliftTangentOrientation_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.uliftTangentOrientation_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.uliftTangentOrientation_apply ``Submission.DifferentialGeometry.Topology.uliftTangentOrientation_apply

theorem uliftTangentOrientation_locally_constant (o : ManifoldOrientation I M n) :
    ∀ p x : ULift.{v} M,
    ∀ hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet,
    ∃ U : Set (ULift.{v} M), IsOpen U ∧ x ∈ U ∧
      ∃ hU : U ⊆ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet,
      ∀ y : ULift.{v} M, ∀ hy : y ∈ U,
        Orientation.map (Fin n) (tangentChartEquiv I (ULift.{v} M) p y (hU hy))
          (uliftTangentOrientation I M o y) =
        Orientation.map (Fin n) (tangentChartEquiv I (ULift.{v} M) p x hx)
          (uliftTangentOrientation I M o x) := by
  rintro ⟨p⟩ ⟨x⟩ hx
  have hxM : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) p).baseSet :=
    (mem_trivializationAt_baseSet_ulift I M p x).mp hx
  obtain ⟨W, hWo, hxW, hWm, hW⟩ := o.locally_constant p x hxM
  have hU : ULift.down ⁻¹' W ⊆
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) (ULift.up p)).baseSet := by
    rintro ⟨y⟩ hy
    exact (mem_trivializationAt_baseSet_ulift I M p y).mpr (hWm hy)
  refine ⟨ULift.down ⁻¹' W, hWo.preimage continuous_uliftDown, hxW, hU, ?_⟩
  rintro ⟨y⟩ hy
  rw [uliftTangentOrientation_apply, uliftTangentOrientation_apply,
    tangentChartEquiv_ulift I M p y (hU hy) (hWm hy),
    tangentChartEquiv_ulift I M p x hx hxM]
  exact hW y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.uliftTangentOrientation_locally_constant then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.uliftTangentOrientation_locally_constant"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.uliftTangentOrientation_locally_constant ``Submission.DifferentialGeometry.Topology.uliftTangentOrientation_locally_constant

def uliftOrientation (o : ManifoldOrientation I M n) : ManifoldOrientation I (ULift.{v} M) n where
  dimension_eq := o.dimension_eq
  orientation := uliftTangentOrientation I M o
  locally_constant := uliftTangentOrientation_locally_constant I M o

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.uliftOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.uliftOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.uliftOrientation ``Submission.DifferentialGeometry.Topology.uliftOrientation

theorem uliftDiffeomorph_preservesOrientation (o : ManifoldOrientation I M n) :
    (uliftDiffeomorph I M).preservesOrientation o (uliftOrientation I M o) := by
  intro x
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.uliftDiffeomorph_preservesOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.uliftDiffeomorph_preservesOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.uliftDiffeomorph_preservesOrientation ``Submission.DifferentialGeometry.Topology.uliftDiffeomorph_preservesOrientation

namespace ClosedOrientedManifold

def ulift (M : ClosedOrientedManifold.{u} n) : ClosedOrientedManifold.{max u v} n where
  Carrier := ULift.{v} M.Carrier
  orientation := uliftOrientation _ _ M.orientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.ulift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.ulift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.ulift ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.ulift

@[simp]
theorem ulift_carrier (M : ClosedOrientedManifold.{u} n) :
    (ulift.{u, v} M).Carrier = ULift.{v} M.Carrier := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.ulift_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.ulift_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.ulift_carrier ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.ulift_carrier

def uliftDiffeomorph (M : ClosedOrientedManifold.{u} n) :
    M.Carrier ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)),
      𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ (ulift.{u, v} M).Carrier :=
  DifferentialGeometry.Topology.uliftDiffeomorph _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.uliftDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.uliftDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.uliftDiffeomorph ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.uliftDiffeomorph

theorem uliftDiffeomorph_preservesOrientation (M : ClosedOrientedManifold.{u} n) :
    (uliftDiffeomorph.{u, v} M).preservesOrientation M.orientation (ulift.{u, v} M).orientation :=
  DifferentialGeometry.Topology.uliftDiffeomorph_preservesOrientation _ _ M.orientation

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.uliftDiffeomorph_preservesOrientation then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.uliftDiffeomorph_preservesOrientation"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.uliftDiffeomorph_preservesOrientation ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.uliftDiffeomorph_preservesOrientation

def uliftOrientedDiffeomorph (M : ClosedOrientedManifold.{u} n) :
    OrientedDiffeomorph M (ulift.{u, v} M) :=
  ⟨uliftDiffeomorph M, uliftDiffeomorph_preservesOrientation M⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ClosedOrientedManifold.uliftOrientedDiffeomorph then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ClosedOrientedManifold.uliftOrientedDiffeomorph"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ClosedOrientedManifold.uliftOrientedDiffeomorph ``Submission.DifferentialGeometry.Topology.ClosedOrientedManifold.uliftOrientedDiffeomorph

end ClosedOrientedManifold

namespace ConnectedClosedOrientedManifold

def ulift (M : ConnectedClosedOrientedManifold.{u} n) :
    ConnectedClosedOrientedManifold.{max u v} n where
  toClosedOrientedManifold := ClosedOrientedManifold.ulift.{u, v} M.toClosedOrientedManifold
  connected :=
    (Homeomorph.ulift : ULift.{v} M.Carrier ≃ₜ M.Carrier).connectedSpace_iff.mpr inferInstance

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.ulift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.ulift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.ulift ``Submission.DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.ulift

@[simp]
theorem ulift_carrier (M : ConnectedClosedOrientedManifold.{u} n) :
    (ulift.{u, v} M).Carrier = ULift.{v} M.Carrier := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.ulift_carrier then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.ulift_carrier"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.ulift_carrier ``Submission.DifferentialGeometry.Topology.ConnectedClosedOrientedManifold.ulift_carrier

end ConnectedClosedOrientedManifold

end DifferentialGeometry.Topology
