import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Submission.DifferentialGeometry.Topology.VectorField.Linearization

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

set_option autoImplicit false

open _root_.Bundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff _root_.Topology

noncomputable section

namespace DifferentialGeometry.VectorField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

section BundleMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

theorem mfderiv_tangentBundle {f : N → TangentBundle I M} {x : N}
    (hf : MDifferentiableAt J I.tangent f x) :
    mfderiv J I.tangent f x =
      (mfderiv J I (fun y => (f y).proj) x).prod
        (mfderiv J 𝓘(𝕜, E)
          (fun y => (_root_.FiberBundle.trivializationAt E (TangentSpace I) (f x).proj (f y)).2) x) := by
  obtain ⟨hb, hv⟩ := (mdifferentiableAt_totalSpace I f).mp hf
  rw [← mfderiv_prodMk hb hv, hf.mfderiv, (hb.prodMk hv).mfderiv]
  congr 1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.mfderiv_tangentBundle then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.mfderiv_tangentBundle"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.mfderiv_tangentBundle ``Submission.DifferentialGeometry.VectorField.mfderiv_tangentBundle

end BundleMap

theorem mfderiv_tangentBundle_proj_apply (p : TangentBundle I M)
    (w : TangentSpace I.tangent p) :
    mfderiv I.tangent I (Bundle.TotalSpace.proj : TangentBundle I M → M) p w = w.1 := by
  have hh := mfderiv_tangentBundle (I := I) (J := I.tangent)
    (f := id) (x := p) mdifferentiableAt_id
  rw [mfderiv_id] at hh
  have hval := congrArg (fun L : TangentSpace I.tangent p →L[𝕜]
      TangentSpace I.tangent p => (L w).1) hh
  exact hval.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.mfderiv_tangentBundle_proj_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.mfderiv_tangentBundle_proj_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.mfderiv_tangentBundle_proj_apply ``Submission.DifferentialGeometry.VectorField.mfderiv_tangentBundle_proj_apply

def verticalLift (x : M) : TangentSpace I x →L[𝕜]
    TangentSpace I.tangent (_root_.Bundle.zeroSection E (TangentSpace I) x) :=
  ContinuousLinearMap.inr 𝕜 (TangentSpace I x) (TangentSpace I x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.verticalLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.verticalLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.verticalLift ``Submission.DifferentialGeometry.VectorField.verticalLift

@[simp]
theorem verticalLift_apply (x : M) (v : TangentSpace I x) :
    verticalLift (I := I) x v = (0, v) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.verticalLift_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.verticalLift_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.verticalLift_apply ``Submission.DifferentialGeometry.VectorField.verticalLift_apply

theorem mfderiv_tangentBundle_proj_verticalLift (x : M) (v : TangentSpace I x) :
    mfderiv I.tangent I (Bundle.TotalSpace.proj : TangentBundle I M → M)
      (_root_.Bundle.zeroSection E (TangentSpace I) x) (verticalLift x v) = 0 := by
  rw [mfderiv_tangentBundle_proj_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.mfderiv_tangentBundle_proj_verticalLift then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.mfderiv_tangentBundle_proj_verticalLift"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.mfderiv_tangentBundle_proj_verticalLift ``Submission.DifferentialGeometry.VectorField.mfderiv_tangentBundle_proj_verticalLift

theorem verticalLift_eq_mfderiv_fiberCurve (x : M) (v : TangentSpace I x) :
    verticalLift (I := I) x v =
      mfderiv 𝓘(𝕜, 𝕜) I.tangent
        (fun t : 𝕜 => (⟨x, t • v⟩ : TangentBundle I M)) 0 (1 : 𝕜) := by
  symm
  have heq : (fun t : 𝕜 =>
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x (⟨x, t • v⟩ : TangentBundle I M)).2) =
      (fun t : 𝕜 => t • v) := by
    funext t
    change tangentCoordChange I x x x (t • v) = t • v
    exact tangentCoordChange_self (mem_extChartAt_source x)
  have hd : MDifferentiableAt 𝓘(𝕜, 𝕜) I.tangent
      (fun t : 𝕜 => (⟨x, t • v⟩ : TangentBundle I M)) 0 := by
    rw [mdifferentiableAt_totalSpace]
    refine ⟨mdifferentiableAt_const, ?_⟩
    rw [heq]
    exact mdifferentiableAt_id.smul mdifferentiableAt_const
  rw [mfderiv_tangentBundle hd]
  change ((mfderiv 𝓘(𝕜, 𝕜) I (fun _ : 𝕜 => x) 0) (1 : 𝕜),
    (mfderiv 𝓘(𝕜, 𝕜) 𝓘(𝕜, E) _ 0) (1 : 𝕜)) = _
  rw [heq]
  change ((mfderiv 𝓘(𝕜, 𝕜) I (fun _ : 𝕜 => x) 0) (1 : 𝕜),
    (mfderiv (M' := E) 𝓘(𝕜, 𝕜) 𝓘(𝕜, E) (fun t : 𝕜 => t • v : 𝕜 → E) 0) (1 : 𝕜)) = _
  rw [mfderiv_const]
  erw [mfderiv_eq_fderiv]
  let w : E := v
  change ((0 : E), (fderiv 𝕜 (fun t : 𝕜 => t • w) 0) 1) = (0, w)
  simp [fderiv_fun_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.verticalLift_eq_mfderiv_fiberCurve then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.verticalLift_eq_mfderiv_fiberCurve"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.verticalLift_eq_mfderiv_fiberCurve ``Submission.DifferentialGeometry.VectorField.verticalLift_eq_mfderiv_fiberCurve


theorem mfderiv_zeroSection_apply (x : M) (v : TangentSpace I x) :
    mfderiv I I.tangent (_root_.Bundle.zeroSection E (TangentSpace I)) x v = (v, 0) := by
  exact congrArg (fun p : TangentBundle I.tangent (TangentBundle I M) => p.2)
    (TangentBundle.tangentMap_tangentBundle_pure (I := I) (⟨x, v⟩ : TangentBundle I M))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.mfderiv_zeroSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.mfderiv_zeroSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.mfderiv_zeroSection_apply ``Submission.DifferentialGeometry.VectorField.mfderiv_zeroSection_apply

theorem mfderiv_section {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x) :
    mfderiv I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x =
      (ContinuousLinearMap.id 𝕜 (TangentSpace I x)).prod
        (mfderiv I 𝓘(𝕜, E)
          (fun y => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x ⟨y, V y⟩).2) x) := by
  rw [mfderiv_tangentBundle hV]
  congr 1
  exact mfderiv_id

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.mfderiv_section then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.mfderiv_section"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.mfderiv_section ``Submission.DifferentialGeometry.VectorField.mfderiv_section

theorem existsUnique_vertical_linearization {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hzero : V x = 0) :
    ∃! L : TangentSpace I x →L[𝕜] TangentSpace I x,
      ∀ v : TangentSpace I x,
        tangentMap I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) ⟨x, v⟩ =
          ⟨zeroSection E (TangentSpace I) x,
            mfderiv I I.tangent (_root_.Bundle.zeroSection E (TangentSpace I)) x v + verticalLift x (L v)⟩ := by
  let L : TangentSpace I x →L[𝕜] TangentSpace I x :=
    mfderiv I 𝓘(𝕜, E) (fun y => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x ⟨y, V y⟩).2) x
  refine ⟨L, ?_, ?_⟩
  · intro v
    rw [tangentMap, mfderiv_section hV, mfderiv_zeroSection_apply]
    simp only [hzero, _root_.Bundle.zeroSection, TotalSpace.mk.injEq, true_and]
    apply heq_of_eq
    change (v, L v) = (v + 0, 0 + L v)
    simp only [add_zero, zero_add]
  · intro K hK
    ext v
    have hh := congrArg (fun p : TangentBundle I.tangent (TangentBundle I M) => p.2.2) (hK v)
    rw [tangentMap, mfderiv_section hV, mfderiv_zeroSection_apply] at hh
    change L v = 0 + K v at hh
    simpa only [zero_add] using hh.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.existsUnique_vertical_linearization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.existsUnique_vertical_linearization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.existsUnique_vertical_linearization ``Submission.DifferentialGeometry.VectorField.existsUnique_vertical_linearization

def linearizationAtZero {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hzero : V x = 0) : TangentSpace I x →L[𝕜] TangentSpace I x :=
  (existsUnique_vertical_linearization hV hzero).exists.choose

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.linearizationAtZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.linearizationAtZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.linearizationAtZero ``Submission.DifferentialGeometry.VectorField.linearizationAtZero


theorem tangentMap_section_eq_linearizationAtZero
    {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hzero : V x = 0) (v : TangentSpace I x) :
    tangentMap I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) ⟨x, v⟩ =
      ⟨zeroSection E (TangentSpace I) x,
        mfderiv I I.tangent (_root_.Bundle.zeroSection E (TangentSpace I)) x v +
          verticalLift x (linearizationAtZero hV hzero v)⟩ :=
  (existsUnique_vertical_linearization hV hzero).exists.choose_spec v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.tangentMap_section_eq_linearizationAtZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.tangentMap_section_eq_linearizationAtZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.tangentMap_section_eq_linearizationAtZero ``Submission.DifferentialGeometry.VectorField.tangentMap_section_eq_linearizationAtZero

theorem linearizationAtZero_eq_mfderiv
    {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hzero : V x = 0) :
    linearizationAtZero hV hzero =
      mfderiv I 𝓘(𝕜, E)
        (fun y => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x ⟨y, V y⟩).2) x := by
  ext v
  have hh := congrArg (fun p : TangentBundle I.tangent (TangentBundle I M) => p.2.2)
    (tangentMap_section_eq_linearizationAtZero hV hzero v)
  rw [tangentMap, mfderiv_section hV, mfderiv_zeroSection_apply] at hh
  change (mfderiv I 𝓘(𝕜, E)
    (fun y => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x ⟨y, V y⟩).2) x) v =
      (0 : TangentSpace I x) + linearizationAtZero hV hzero v at hh
  rw [zero_add] at hh
  exact hh.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.linearizationAtZero_eq_mfderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.linearizationAtZero_eq_mfderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.linearizationAtZero_eq_mfderiv ``Submission.DifferentialGeometry.VectorField.linearizationAtZero_eq_mfderiv

theorem linearizationAtZero_congr_of_eventuallyEq
    {V W : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hW : MDifferentiableAt I I.tangent (fun y => (⟨y, W y⟩ : TangentBundle I M)) x)
    (hVzero : V x = 0) (hWzero : W x = 0)
    (heq : (fun y => (⟨y, V y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
      (fun y => (⟨y, W y⟩ : TangentBundle I M))) :
    linearizationAtZero hV hVzero = linearizationAtZero hW hWzero := by
  rw [linearizationAtZero_eq_mfderiv, linearizationAtZero_eq_mfderiv]
  apply Filter.EventuallyEq.mfderiv_eq
  filter_upwards [heq] with y hy
  exact congrArg (fun p : TangentBundle I M =>
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) x p).2) hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.linearizationAtZero_congr_of_eventuallyEq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.linearizationAtZero_congr_of_eventuallyEq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.linearizationAtZero_congr_of_eventuallyEq ``Submission.DifferentialGeometry.VectorField.linearizationAtZero_congr_of_eventuallyEq

theorem linearizationAtZero_eq_fderivWithin
    {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hzero : V x = 0) :
    linearizationAtZero hV hzero =
      fderivWithin 𝕜
        (fun z : E => (_root_.FiberBundle.trivializationAt E (TangentSpace I) x
          (⟨(extChartAt I x).symm z, V ((extChartAt I x).symm z)⟩ : TangentBundle I M)).2)
        (_root_.Set.range I) (extChartAt I x x) := by
  rw [linearizationAtZero_eq_mfderiv hV hzero]
  exact ((mdifferentiableAt_section I V).mp hV).mfderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.linearizationAtZero_eq_fderivWithin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.linearizationAtZero_eq_fderivWithin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.linearizationAtZero_eq_fderivWithin ``Submission.DifferentialGeometry.VectorField.linearizationAtZero_eq_fderivWithin

theorem linearizationAtZero_modelSpace_eq_fderiv {V : E → E} {x : E}
    (hV : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent
      (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(𝕜, E) E)) x) (hzero : V x = 0) :
    linearizationAtZero hV hzero = fderiv 𝕜 V x := by
  rw [linearizationAtZero_eq_fderivWithin hV hzero]
  simp only [mfld_simps, fderivWithin_univ]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.linearizationAtZero_modelSpace_eq_fderiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.linearizationAtZero_modelSpace_eq_fderiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.linearizationAtZero_modelSpace_eq_fderiv ``Submission.DifferentialGeometry.VectorField.linearizationAtZero_modelSpace_eq_fderiv

theorem fromTangentSpace_linearizationAtZero {V : E → E} {x : E}
    (hV : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent
      (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(𝕜, E) E)) x) (hzero : V x = 0) :
    (NormedSpace.fromTangentSpace x).toContinuousLinearMap ∘L
      linearizationAtZero hV hzero ∘L
        (NormedSpace.fromTangentSpace x).symm.toContinuousLinearMap = fderiv 𝕜 V x := by
  rw [linearizationAtZero_modelSpace_eq_fderiv]
  ext v
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.VectorField.fromTangentSpace_linearizationAtZero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.VectorField.fromTangentSpace_linearizationAtZero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.VectorField.fromTangentSpace_linearizationAtZero ``Submission.DifferentialGeometry.VectorField.fromTangentSpace_linearizationAtZero

end DifferentialGeometry.VectorField
