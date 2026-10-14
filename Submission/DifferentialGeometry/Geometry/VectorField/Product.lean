import Submission.DifferentialGeometry.Topology.Manifold.LieBracketNaturality
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Bundle
open scoped _root_.Manifold _root_.ContDiff

namespace DifferentialGeometry.Geometry.VectorField

variable {E H M F K N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N]

def productVectorField
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (Y : ContMDiffSection J F ∞ (TangentSpace J : N → Type _)) :
    ContMDiffSection (I.prod J) (E × F) ∞ (TangentSpace (I.prod J) : M × N → Type _) where
  toFun x := (X x.1, Y x.2)
  contMDiff_toFun := (contMDiff_equivTangentBundleProd_symm
    (I := I) (I' := J) (M := M) (M' := N)).comp (X.contMDiff.prodMap Y.contMDiff)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.VectorField.productVectorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.VectorField.productVectorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.VectorField.productVectorField ``Submission.DifferentialGeometry.Geometry.VectorField.productVectorField

@[simp] theorem productVectorField_apply
    (X : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (Y : ContMDiffSection J F ∞ (TangentSpace J : N → Type _)) (x : M × N) :
    productVectorField X Y x = (X x.1, Y x.2) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.VectorField.productVectorField_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.VectorField.productVectorField_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.VectorField.productVectorField_apply ``Submission.DifferentialGeometry.Geometry.VectorField.productVectorField_apply

theorem mlieBracket_productVectorField
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [T2Space M] [T2Space N]
    (X Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (X' Y' : ContMDiffSection J F ∞ (TangentSpace J : N → Type _)) (x : M × N) :
    _root_.VectorField.mlieBracket (I.prod J) (productVectorField X X')
      (productVectorField Y Y') x =
        (_root_.VectorField.mlieBracket I X Y x.1,
          _root_.VectorField.mlieBracket J X' Y' x.2) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  have h1 := DifferentialGeometry.Topology.Manifold.mfderiv_mlieBracket_of_related
    (φ := Prod.fst) (J := I) contMDiff_fst (productVectorField X X')
    (productVectorField Y Y') X Y
    (fun y ↦ by rw [mfderiv_fst]; rfl) (fun y ↦ by rw [mfderiv_fst]; rfl) x
  have h2 := DifferentialGeometry.Topology.Manifold.mfderiv_mlieBracket_of_related
    (φ := Prod.snd) (J := J) contMDiff_snd (productVectorField X X')
    (productVectorField Y Y') X' Y'
    (fun y ↦ by rw [mfderiv_snd]; rfl) (fun y ↦ by rw [mfderiv_snd]; rfl) x
  rw [mfderiv_fst] at h1
  rw [mfderiv_snd] at h2
  exact Prod.ext h1 h2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.VectorField.mlieBracket_productVectorField then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.VectorField.mlieBracket_productVectorField"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.VectorField.mlieBracket_productVectorField ``Submission.DifferentialGeometry.Geometry.VectorField.mlieBracket_productVectorField

end DifferentialGeometry.Geometry.VectorField
