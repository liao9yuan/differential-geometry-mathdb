import Submission.DifferentialGeometry.Geometry.Coordinates.Frame.Chart
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartCoeff (x₀ : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun x => (chartModelBasis E).repr
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀) ⟨x, X x⟩).2 i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartCoeff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartCoeff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartCoeff ``Submission.DifferentialGeometry.Tensor.Coordinates.chartCoeff

@[simp] lemma chartCoeff_def (x₀ : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) (x : M) :
    chartCoeff (I := I) x₀ X i x =
      (chartModelBasis E).repr
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀) ⟨x, X x⟩).2 i := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartCoeff_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartCoeff_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartCoeff_def ``Submission.DifferentialGeometry.Tensor.Coordinates.chartCoeff_def

lemma chartCoeff_recompose (x₀ : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    {x : M} (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) :
    X x = ∑ i, chartCoeff (I := I) x₀ X i x •
      chartBasisVecFiber (I := I) x₀ i x := by
  classical
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    _root_.FiberBundle.trivializationAt E (TangentSpace I) x₀
  set L : TangentSpace I x ≃L[ℝ] E := T.continuousLinearEquivAt ℝ x hx
  have hL : L (X x) = (T ⟨x, X x⟩).2 := rfl
  have hLsymm : ∀ v : E, L.symm v = T.symmL ℝ x v := fun v =>
    congrFun (T.symm_continuousLinearEquivAt_eq hx) v
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E
  have hdecomp : (T ⟨x, X x⟩).2 =
      ∑ i, b.repr ((T ⟨x, X x⟩).2) i • b i := by
    have h := Module.Basis.sum_repr b ((T ⟨x, X x⟩).2)
    exact h.symm
  have hX : X x = L.symm ((T ⟨x, X x⟩).2) := by
    rw [← hL, L.symm_apply_apply]
  rw [hX, hdecomp, map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [map_smul, hLsymm]
  simp only [chartCoeff_def, chartBasisVecFiber]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartCoeff_recompose then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartCoeff_recompose"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartCoeff_recompose ``Submission.DifferentialGeometry.Tensor.Coordinates.chartCoeff_recompose

lemma chartCoeff_contMDiffOn (x₀ : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartCoeff (I := I) x₀ X i)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by
  classical
  set T : Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    _root_.FiberBundle.trivializationAt E (TangentSpace I) x₀
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% fun x : M => X x) := X.contMDiff
  have hiff :=
    T.contMDiffOn_section_baseSet_iff (IB := I) (n := ∞)
      (s := fun x : M => X x)
  have hsection : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun x : M => (T ⟨x, X x⟩).2) T.baseSet := hiff.mp hX.contMDiffOn
  set b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E
  set Lcoord : E →L[ℝ] ℝ := (b.coord i).toContinuousLinearMap
  have hLcoord_contDiff : ContDiff ℝ ∞ (Lcoord : E → ℝ) := Lcoord.contDiff
  have hcomp : ContMDiffOn I 𝓘(ℝ) ∞
      ((Lcoord : E → ℝ) ∘ (fun x : M => (T ⟨x, X x⟩).2)) T.baseSet :=
    hLcoord_contDiff.contMDiff.comp_contMDiffOn hsection
  have heq : (Lcoord : E → ℝ) ∘ (fun x : M => (T ⟨x, X x⟩).2) =
      chartCoeff (I := I) x₀ X i := by
    funext x
    change Lcoord ((T ⟨x, X x⟩).2) =
      (chartModelBasis E).repr
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀) ⟨x, X x⟩).2 i
    change (b.coord i) ((T ⟨x, X x⟩).2) = _
    rw [Module.Basis.coord_apply]
  rw [← heq]
  exact hcomp

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartCoeff_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartCoeff_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartCoeff_contMDiffOn ``Submission.DifferentialGeometry.Tensor.Coordinates.chartCoeff_contMDiffOn

def chartCoeffOnE (x₀ : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartCoeff (I := I) x₀ X i ((extChartAt I x₀).symm y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartCoeffOnE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartCoeffOnE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartCoeffOnE ``Submission.DifferentialGeometry.Tensor.Coordinates.chartCoeffOnE

lemma chartCoeffOnE_contDiffOn (x₀ : M)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartCoeffOnE (I := I) x₀ X i)
      (extChartAt I x₀).target := by
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞ (chartCoeff (I := I) x₀ X i)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
    chartCoeff_contMDiffOn (I := I) x₀ X i
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm
      (extChartAt I x₀).target := contMDiffOn_extChartAt_symm (I := I) x₀
  have hsubset : (extChartAt I x₀).target ⊆
      (extChartAt I x₀).symm ⁻¹'
        (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
    fun _ hy => extChartAt_symm_mem_trivializationAt_baseSet (I := I) x₀ hy
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((chartCoeff (I := I) x₀ X i) ∘ (extChartAt I x₀).symm)
      (extChartAt I x₀).target := hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartCoeffOnE_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartCoeffOnE_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartCoeffOnE_contDiffOn ``Submission.DifferentialGeometry.Tensor.Coordinates.chartCoeffOnE_contDiffOn

end DifferentialGeometry.Tensor.Coordinates
