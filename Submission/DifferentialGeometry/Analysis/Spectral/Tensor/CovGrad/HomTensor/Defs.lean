import Submission.DifferentialGeometry.Geometry.Connection.TensorNabla.TensorRS.Basic
import Submission.DifferentialGeometry.Analysis.Spectral.Tensor.CovGrad.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.IsManifold _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators


namespace DifferentialGeometry.Geometry.Connection

section ModelFiber

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

def HomTensorRSModel (r a c : ℕ) (𝕜 : Type*) (E : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] :=
  TensorRSModel r a 𝕜 E →L[𝕜] TensorRSModel r c 𝕜 E

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.HomTensorRSModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.HomTensorRSModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.HomTensorRSModel ``Submission.DifferentialGeometry.Geometry.Connection.HomTensorRSModel

private instance tensor0SModel_smulCommClass (s : ℕ) :
    SMulCommClass 𝕜 𝕜 (Tensor0SModel s 𝕜 E) := by
  unfold Tensor0SModel
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.tensor0SModel_smulCommClass
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.tensor0SModel_smulCommClass target :: scope.openDecls } }

private instance tensorRSModel_smulCommClass (r c : ℕ) :
    SMulCommClass 𝕜 𝕜 (TensorRSModel r c 𝕜 E) := by
  let : NormedSpace 𝕜 (Tensor0SModel r 𝕜 E) := tensor0SModelNormedSpace r
  let : NormedSpace 𝕜 (Tensor0SModel c 𝕜 E) := tensor0SModelNormedSpace c
  unfold TensorRSModel
  infer_instance

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.tensorRSModel_smulCommClass
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.tensorRSModel_smulCommClass target :: scope.openDecls } }

instance homTensorRSModelNormedAddCommGroup (r a c : ℕ) :
    NormedAddCommGroup (HomTensorRSModel r a c 𝕜 E) := by
  unfold HomTensorRSModel
  letI nsU : NormedSpace 𝕜 (TensorRSModel r a 𝕜 E) := tensorRSModelNormedSpace r a
  letI nsV : NormedSpace 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModelNormedSpace r c
  exact @ContinuousLinearMap.toNormedAddCommGroup 𝕜 𝕜
    (TensorRSModel r a 𝕜 E) (TensorRSModel r c 𝕜 E) _ _ _ _ nsU nsV _ _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSModelNormedAddCommGroup then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSModelNormedAddCommGroup"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSModelNormedAddCommGroup ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSModelNormedAddCommGroup

instance homTensorRSModelNormedSpace (r a c : ℕ) :
    NormedSpace 𝕜 (HomTensorRSModel r a c 𝕜 E) := by
  unfold HomTensorRSModel
  letI nsU : NormedSpace 𝕜 (TensorRSModel r a 𝕜 E) := tensorRSModelNormedSpace r a
  letI nsV : NormedSpace 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModelNormedSpace r c
  letI scc : SMulCommClass 𝕜 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModel_smulCommClass r c
  exact @ContinuousLinearMap.toNormedSpace 𝕜 𝕜
    (TensorRSModel r a 𝕜 E) (TensorRSModel r c 𝕜 E) _ _ _ _ _ _ _ _ 𝕜 _ nsV scc

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSModelNormedSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSModelNormedSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSModelNormedSpace ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSModelNormedSpace

noncomputable instance homTensorRSModel_finiteDimensional (r a c : ℕ) :
    @FiniteDimensional 𝕜 (HomTensorRSModel r a c 𝕜 E) _
      (homTensorRSModelNormedAddCommGroup r a c).toAddCommGroup
      (homTensorRSModelNormedSpace r a c).toModule := by
  let nsU : NormedSpace 𝕜 (TensorRSModel r a 𝕜 E) := tensorRSModelNormedSpace r a
  let nsV : NormedSpace 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModelNormedSpace r c
  have iUf : FiniteDimensional 𝕜 (TensorRSModel r a 𝕜 E) := tensorRSModel_finiteDimensional r a
  have iVf : FiniteDimensional 𝕜 (TensorRSModel r c 𝕜 E) := tensorRSModel_finiteDimensional r c
  unfold HomTensorRSModel
  exact ContinuousLinearMap.finiteDimensional

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSModel_finiteDimensional then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSModel_finiteDimensional"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSModel_finiteDimensional ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSModel_finiteDimensional

end ModelFiber

section SpaceFiber

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

abbrev HomTensorRSSpace (r a c : ℕ) (I : ModelWithCorners 𝕜 E H) [IsManifold I 1 M] (x : M) : Type
    _ :=
  TensorRSSpace r a I x →L[𝕜] TensorRSSpace r c I x

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.HomTensorRSSpace then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.HomTensorRSSpace"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.HomTensorRSSpace ``Submission.DifferentialGeometry.Geometry.Connection.HomTensorRSSpace

noncomputable instance homTensorRSBundleTopology (r a c : ℕ) :
    TopologicalSpace (_root_.Bundle.TotalSpace (HomTensorRSModel r a c 𝕜 E)
      (fun x : M => HomTensorRSSpace r a c I x)) :=
  Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace (RingHom.id 𝕜)
    (TensorRSModel r a 𝕜 E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c 𝕜 E) (fun x : M => TensorRSSpace r c I x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSBundleTopology then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSBundleTopology"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSBundleTopology ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSBundleTopology

noncomputable instance homTensorRSBundleFiber (r a c : ℕ) :
    @FiberBundle M (HomTensorRSModel r a c 𝕜 E) _ (by infer_instance : TopologicalSpace _)
      (fun x : M => HomTensorRSSpace r a c I x)
      (homTensorRSBundleTopology r a c) _ :=
  Bundle.ContinuousLinearMap.fiberBundle (RingHom.id 𝕜)
    (TensorRSModel r a 𝕜 E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c 𝕜 E) (fun x : M => TensorRSSpace r c I x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSBundleFiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSBundleFiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSBundleFiber ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSBundleFiber

noncomputable instance homTensorRSBundle_vector (r a c : ℕ) :
    @VectorBundle 𝕜 M (HomTensorRSModel r a c 𝕜 E) (fun x : M => HomTensorRSSpace r a c I x) _
      (fun x => by infer_instance) (fun x => by infer_instance)
      (homTensorRSModelNormedAddCommGroup r a c) (homTensorRSModelNormedSpace r a c) _
      (homTensorRSBundleTopology r a c) _
      (homTensorRSBundleFiber r a c) :=
  Bundle.ContinuousLinearMap.vectorBundle (RingHom.id 𝕜)
    (TensorRSModel r a 𝕜 E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c 𝕜 E) (fun x : M => TensorRSSpace r c I x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSBundle_vector then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSBundle_vector"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSBundle_vector ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSBundle_vector

noncomputable instance homTensorRSBundle_smooth (n : WithTop ℕ∞)
    [IsManifold I (n + 1) M] (r a c : ℕ) :
    @ContMDiffVectorBundle n 𝕜 M (HomTensorRSModel r a c 𝕜 E)
      (fun x : M => HomTensorRSSpace r a c I x)
      _ E _ _ H _ I _ _ _ _ _ _
      (homTensorRSBundleTopology r a c) _
      (homTensorRSBundleFiber r a c)
      (homTensorRSBundle_vector r a c) :=
  ContMDiffVectorBundle.continuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSBundle_smooth then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSBundle_smooth"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSBundle_smooth ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSBundle_smooth

end SpaceFiber

section CovDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

open _root_.CovariantDerivative _root_.Submission.CovariantDerivative _root_.Submission.DifferentialGeometry.Geometry.Curvature.CovariantDerivative

noncomputable def homTensorRSCovariantDerivative (r a c : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    CovariantDerivative I (HomTensorRSModel r a c ℝ E)
      (fun x : M => HomTensorRSSpace r a c I x) :=
  HomConnection.homBundleCovariantDerivative I M
    (TensorRSModel r a ℝ E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c ℝ E) (fun x : M => TensorRSSpace r c I x)
    (TensorRSNabla.tensorRSCovariantDerivative I M r a cov)
    (TensorRSNabla.tensorRSCovariantDerivative I M r c cov)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative

noncomputable instance homTensorRSCovariantDerivative_contMDiff (r a c : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivative (homTensorRSCovariantDerivative I M r a c cov) ∞ :=
  HomConnection.homBundleCovariantDerivative_contMDiff I M
    (TensorRSModel r a ℝ E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c ℝ E) (fun x : M => TensorRSSpace r c I x)
    (TensorRSNabla.tensorRSCovariantDerivative I M r a cov)
    (TensorRSNabla.tensorRSCovariantDerivative I M r c cov)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_contMDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_contMDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_contMDiff ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_contMDiff

omit [CompleteSpace E] in
theorem homTensorRSCovariantDerivative_contMDiffOn (r a c : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞] :
    ContMDiffCovariantDerivativeOn (HomTensorRSModel r a c ℝ E) ∞
      (homTensorRSCovariantDerivative I M r a c cov).toFun Set.univ := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  exact (homTensorRSCovariantDerivative_contMDiff I M r a c cov).contMDiff

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_contMDiffOn ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_contMDiffOn

omit [CompleteSpace E] in
theorem homTensorRSCovariantDerivative_section_contMDiffOn (r a c : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (Ψ : Π x : M, HomTensorRSSpace r a c I x)
    (hΨ : ContMDiff I (I.prod 𝓘(ℝ, HomTensorRSModel r a c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (HomTensorRSModel r a c ℝ E)
        (E := fun z : M => HomTensorRSSpace r a c I z) x (Ψ x))) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] HomTensorRSModel r a c ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] HomTensorRSModel r a c ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] HomTensorRSSpace r a c I z) x
        ((homTensorRSCovariantDerivative I M r a c cov).toFun Ψ x)) Set.univ := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h_le : ((∞ : WithTop ℕ∞) + 1) ≤ (∞ : WithTop ℕ∞) := by rw [ENat.coe_top_add_one]
  exact (homTensorRSCovariantDerivative_contMDiffOn I M r a c cov).contMDiff
    (σ := Ψ) ((hΨ.of_le h_le).contMDiffOn)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_section_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_section_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_section_contMDiffOn ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_section_contMDiffOn

omit [CompleteSpace E] in
theorem homTensorRSCovariantDerivative_apply (r a c : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (Ψ : Cₛ^∞⟮I; HomTensorRSModel r a c ℝ E, (fun x : M => HomTensorRSSpace r a c I x)⟯)
    (W : Cₛ^∞⟮I; TensorRSModel r a ℝ E, (fun x : M => TensorRSSpace r a I x)⟯)
    (x : M) (v : TangentSpace I x) :
    (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
        homTensorRSCovariantDerivative I M r a c cov Ψ x v) (W x) =
      TensorRSNabla.tensorRSCovariantDerivative I M r c cov
        (fun y =>
          (show TensorRSSpace r a I y →L[ℝ] TensorRSSpace r c I y from Ψ y) (W y)) x v -
      (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Ψ x)
        (TensorRSNabla.tensorRSCovariantDerivative I M r a cov W x v) :=
  HomConnection.homBundleCovariantDerivative_apply I M
    (TensorRSModel r a ℝ E) (fun x : M => TensorRSSpace r a I x)
    (TensorRSModel r c ℝ E) (fun x : M => TensorRSSpace r c I x)
    (TensorRSNabla.tensorRSCovariantDerivative I M r a cov)
    (TensorRSNabla.tensorRSCovariantDerivative I M r c cov)
    Ψ W x v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_apply ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_apply

omit [CompleteSpace E] in
theorem homTensorRSCovariantDerivative_apply_of_mdifferentiableAt (r a c : ℕ)
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    [_root_.CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (Ψ : Π x : M, TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x)
    (W : Π x : M, TensorRSSpace r a I x)
    (V_field : Π x : M, TangentSpace I x)
    {x : M}
    (hΨ : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r a ℝ E →L[ℝ] TensorRSModel r c ℝ E)
        (E := fun z : M => TensorRSSpace r a I z →L[ℝ] TensorRSSpace r c I z) y (Ψ y)) x)
    (hW : MDifferentiableAt I (I.prod 𝓘(ℝ, TensorRSModel r a ℝ E))
      (fun y : M => TotalSpace.mk' (TensorRSModel r a ℝ E)
        (E := fun z : M => TensorRSSpace r a I z) y (W y)) x)
    (hV : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun y : M => TotalSpace.mk' E
        (E := fun z : M => TangentSpace I z) y (V_field y)) x) :
    (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from
        homTensorRSCovariantDerivative I M r a c cov Ψ x (V_field x)) (W x) =
      TensorRSNabla.tensorRSCovariantDerivative I M r c cov
        (fun y =>
          (show TensorRSSpace r a I y →L[ℝ] TensorRSSpace r c I y from Ψ y) (W y))
          x (V_field x) -
      (show TensorRSSpace r a I x →L[ℝ] TensorRSSpace r c I x from Ψ x)
        (TensorRSNabla.tensorRSCovariantDerivative I M r a cov W x (V_field x)) :=
  HomConnection.homBundleCovariantDerivative_apply_of_mdifferentiableAt I M
    (TensorRSModel r a ℝ E) (fun y : M => TensorRSSpace r a I y)
    (TensorRSModel r c ℝ E) (fun y : M => TensorRSSpace r c I y)
    (TensorRSNabla.tensorRSCovariantDerivative I M r a cov)
    (TensorRSNabla.tensorRSCovariantDerivative I M r c cov)
    Ψ hΨ hV hW

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_apply_of_mdifferentiableAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_apply_of_mdifferentiableAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_apply_of_mdifferentiableAt ``Submission.DifferentialGeometry.Geometry.Connection.homTensorRSCovariantDerivative_apply_of_mdifferentiableAt

end CovDeriv

end DifferentialGeometry.Geometry.Connection

end
