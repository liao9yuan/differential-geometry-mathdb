import Submission.DifferentialGeometry.Tensor.Alternating.BundleMaps
import Submission.DifferentialGeometry.Tensor.Multilinear.Bundle.Section

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff

namespace DifferentialGeometry

abbrev AlternatingSection
    (𝕜 : Type*) [NontriviallyNormedField 𝕜]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    {HB : Type*} [TopologicalSpace HB] (IB : ModelWithCorners 𝕜 EB HB)
    {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
    (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
    [TopologicalSpace (_root_.Bundle.TotalSpace F E)]
    [FiberBundle F E] [VectorBundle 𝕜 F E]
    (n : WithTop ℕ∞) [hSmooth : ContMDiffVectorBundle n F E IB] (s : ℕ) :=
  let _ := hSmooth
  ContMDiffSection IB (F [⋀^Fin s]→L[𝕜] 𝕜) n
    (Bundle.continuousAlternatingMap 𝕜 (Fin s) F E 𝕜 (Bundle.Trivial B 𝕜))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.AlternatingSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.AlternatingSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.AlternatingSection ``Submission.DifferentialGeometry.AlternatingSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
variable {HB : Type*} [TopologicalSpace HB]
variable {IB : ModelWithCorners 𝕜 EB HB}
variable {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
variable {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
variable [TopologicalSpace (TotalSpace F E)]
variable [FiberBundle F E] [VectorBundle 𝕜 F E]
variable {n : WithTop ℕ∞} [ContMDiffVectorBundle n F E IB]

namespace AlternatingSection

noncomputable def toMultilinearSection {s : ℕ}
    (α : AlternatingSection 𝕜 F IB E n s) :
    MultilinearSection 𝕜 F IB E n s :=
  ⟨fun x => (α x).toContinuousMultilinearMap,
    α.contMDiff_toFun.alternating_bundle_toMultilinear⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.AlternatingSection.toMultilinearSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.AlternatingSection.toMultilinearSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.AlternatingSection.toMultilinearSection ``Submission.DifferentialGeometry.AlternatingSection.toMultilinearSection

@[simp] theorem toMultilinearSection_apply {s : ℕ}
    (α : AlternatingSection 𝕜 F IB E n s) (x : B) :
    α.toMultilinearSection x = (α x).toContinuousMultilinearMap :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.AlternatingSection.toMultilinearSection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.AlternatingSection.toMultilinearSection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.AlternatingSection.toMultilinearSection_apply ``Submission.DifferentialGeometry.AlternatingSection.toMultilinearSection_apply

end AlternatingSection

namespace MultilinearSection

noncomputable def alternatization {s : ℕ}
    (α : MultilinearSection 𝕜 F IB E n s) :
    AlternatingSection 𝕜 F IB E n s :=
  ⟨fun x => ContinuousMultilinearMap.alternatizationCLM (α x),
    α.contMDiff_toFun.multilinear_bundle_alternatization⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.alternatization then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.alternatization"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.alternatization ``Submission.DifferentialGeometry.MultilinearSection.alternatization

@[simp] theorem alternatization_apply {s : ℕ}
    (α : MultilinearSection 𝕜 F IB E n s) (x : B) :
    α.alternatization x = ContinuousMultilinearMap.alternatizationCLM (α x) :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.alternatization_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.alternatization_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.alternatization_apply ``Submission.DifferentialGeometry.MultilinearSection.alternatization_apply

@[simp] theorem alternatization_toMultilinearSection [CharZero 𝕜] {s : ℕ}
    (α : AlternatingSection 𝕜 F IB E n s) :
    α.toMultilinearSection.alternatization = α := by
  apply ContMDiffSection.ext
  intro x
  exact ContinuousMultilinearMap.alternatizationCLM_apply_toContinuousMultilinearMap (α x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.MultilinearSection.alternatization_toMultilinearSection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.MultilinearSection.alternatization_toMultilinearSection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.MultilinearSection.alternatization_toMultilinearSection ``Submission.DifferentialGeometry.MultilinearSection.alternatization_toMultilinearSection

end MultilinearSection

end DifferentialGeometry
