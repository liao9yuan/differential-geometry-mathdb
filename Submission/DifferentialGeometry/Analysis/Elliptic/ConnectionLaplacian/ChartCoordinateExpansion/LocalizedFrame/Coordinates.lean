import Submission.DifferentialGeometry.Analysis.Elliptic.ConnectionLaplacian.ChartCoordinateExpansion.LocalizedFrame.Basic
import Submission.DifferentialGeometry.Geometry.Operator.Gradient.Basic

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Analysis.Elliptic
open _root_.Submission.DifferentialGeometry.Geometry.Curvature
open _root_.Submission.DifferentialGeometry.Geometry.Operator

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap _root_.Filter
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators


namespace DifferentialGeometry
namespace Geometry
namespace Connection

open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M]

private local instance _root_.Submission.DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry : CompleteSpace E := FiniteDimensional.complete ℝ E

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.instCompleteSpace_differentialGeometry target :: scope.openDecls } }

noncomputable def chartFrameNormGlobalSmoothCoordMatrix
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) (b : M) : ℝ := by
  classical
  exact
    if h : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet then
      (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) α h).repr
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) k
    else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmoothCoordMatrix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmoothCoordMatrix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmoothCoordMatrix ``Submission.DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmoothCoordMatrix

omit [I.Boundaryless] in
private lemma chartFrameNormGlobalSmoothCoordMatrix_of_mem
    (g : SmoothRiemannianMetric I M) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet) :
    chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b =
      (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) α hb).repr
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b) k := by
  classical
  unfold chartFrameNormGlobalSmoothCoordMatrix
  rw [dif_pos hb]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmoothCoordMatrix_of_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmoothCoordMatrix_of_mem target :: scope.openDecls } }

omit [I.Boundaryless] in
theorem chartFrameNormGlobalSmooth_eq_coordMatrix_sum
    (g : SmoothRiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E))
    {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i :
        Π b : M, TangentSpace I b) b) =
      ∑ k : Fin (Module.finrank ℝ E),
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b •
          DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b := by
  classical
  have hb_base : b ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    chartLeviCivitaGoodSet_mem_baseSet (I := I) hb
  have hsum := (DifferentialGeometry.Tensor.Coordinates.chartBasisFamily (I := I) α hb_base).sum_repr
      ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
  have hcoerce : ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i :
        Π b : M, TangentSpace I b) b)
      = (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b := rfl
  rw [hcoerce]
  rw [← hsum]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [chartFrameNormGlobalSmoothCoordMatrix_of_mem (I := I) (M := M) g α i k hb_base]
  rw [DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply (I := I) α hb_base k]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmooth_eq_coordMatrix_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmooth_eq_coordMatrix_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmooth_eq_coordMatrix_sum ``Submission.DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmooth_eq_coordMatrix_sum

section LinearAlgebra

variable (g : SmoothRiemannianMetric I M) (α : M) {b : M}

private noncomputable def coordMatrixOf (i k : Fin (Module.finrank ℝ E)) : ℝ :=
  chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.coordMatrixOf
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.coordMatrixOf target :: scope.openDecls } }

private noncomputable def coordMatrix :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of (fun i k => coordMatrixOf (I := I) (M := M) g α (b := b) i k)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.coordMatrix
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.coordMatrix target :: scope.openDecls } }

omit [I.Boundaryless] in
@[simp] private lemma coordMatrix_apply (i k : Fin (Module.finrank ℝ E)) :
    coordMatrix (I := I) (M := M) g α (b := b) i k =
      chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.coordMatrix_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.coordMatrix_apply target :: scope.openDecls } }

omit [I.Boundaryless] in
private lemma chartFrameNormGlobalSmooth_eq_coord_sum_of_mem
    (i : Fin (Module.finrank ℝ E))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b =
      ∑ k : Fin (Module.finrank ℝ E),
        coordMatrix (I := I) (M := M) g α (b := b) i k •
          DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b := by
  classical
  have h :=
    chartFrameNormGlobalSmooth_eq_coordMatrix_sum
      (I := I) (M := M) g α i (b := b) hb
  have hcoerce : ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i :
        Π b : M, TangentSpace I b) b)
      = (chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b := rfl
  rw [hcoerce] at h
  rw [h]
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmooth_eq_coord_sum_of_mem
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmooth_eq_coord_sum_of_mem target :: scope.openDecls } }

omit [I.Boundaryless] in
private lemma gram_expand_coordBasis
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (i j : Fin (Module.finrank ℝ E)) :
    g.inner b
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α i).toFun b)
        ((chartFrameNormGlobalSmooth (I := I) (M := M) g α j).toFun b) =
      ∑ k : Fin (Module.finrank ℝ E), ∑ l : Fin (Module.finrank ℝ E),
        coordMatrix (I := I) (M := M) g α (b := b) i k *
          coordMatrix (I := I) (M := M) g α (b := b) j l *
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b k l := by
  classical
  rw [chartFrameNormGlobalSmooth_eq_coord_sum_of_mem (I := I) (M := M) g α i hb]
  rw [chartFrameNormGlobalSmooth_eq_coord_sum_of_mem (I := I) (M := M) g α j hb]
  set v : Fin (Module.finrank ℝ E) → TangentSpace I b :=
    fun k => DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := I) α k b with hv_def
  set a : Fin (Module.finrank ℝ E) → ℝ :=
    fun k => coordMatrix (I := I) (M := M) g α (b := b) i k with ha_def
  set c : Fin (Module.finrank ℝ E) → ℝ :=
    fun l => coordMatrix (I := I) (M := M) g α (b := b) j l with hc_def
  have hL :
      g.inner b (∑ k, a k • v k) =
        ∑ k, a k • g.inner b (v k) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [map_smul]
  rw [hL]
  rw [sum_apply]
  refine Finset.sum_congr rfl ?_
  intro k _
  rw [smul_apply, smul_eq_mul]
  have hR :
      g.inner b (v k) (∑ l, c l • v l) =
        ∑ l, c l * g.inner b (v k) (v l) := by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [map_smul]; rfl
  rw [hR, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_apply]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.gram_expand_coordBasis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.gram_expand_coordBasis target :: scope.openDecls } }

omit [I.Boundaryless] in
private lemma orthonormal_matrix_form_at
    (hb_pou : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    coordMatrix (I := I) (M := M) g α (b := b) *
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b *
          (coordMatrix (I := I) (M := M) g α (b := b)).transpose =
      (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := by
  classical
  ext i j
  have hbpouGood :
      b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ∩
            chartLeviCivitaGoodSet (I := I) α := ⟨hb_pou, hb⟩
  have horth :=
    chartFrameNormGlobalSmooth_orthonormal_on_pouTsupportGoodSet
      (I := I) (M := M) g α (b := b) hbpouGood i j
  have hexp := gram_expand_coordBasis (I := I) (M := M) g α (b := b) hb i j
  rw [horth] at hexp
  rw [Matrix.mul_apply]
  have h_inner : ∀ k₀ : Fin (Module.finrank ℝ E),
      (coordMatrix (I := I) (M := M) g α (b := b) *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b) i k₀ *
        (coordMatrix (I := I) (M := M) g α (b := b)).transpose k₀ j =
      ∑ l₀ : Fin (Module.finrank ℝ E),
        coordMatrix (I := I) (M := M) g α (b := b) i l₀ *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b l₀ k₀ *
          coordMatrix (I := I) (M := M) g α (b := b) j k₀ := by
    intro k₀
    rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [show (∑ k₀, (coordMatrix (I := I) (M := M) g α (b := b) *
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b) i k₀ *
        (coordMatrix (I := I) (M := M) g α (b := b)).transpose k₀ j) =
      ∑ k₀, ∑ l₀,
        coordMatrix (I := I) (M := M) g α (b := b) i l₀ *
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b l₀ k₀ *
          coordMatrix (I := I) (M := M) g α (b := b) j k₀ from
    Finset.sum_congr rfl (fun k₀ _ => h_inner k₀)]
  rw [show (1 : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ) i j =
      (if i = j then (1 : ℝ) else 0) from by
    rw [Matrix.one_apply]]
  rw [hexp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro l₀ _
  refine Finset.sum_congr rfl ?_
  intro k₀ _
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.orthonormal_matrix_form_at
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.orthonormal_matrix_form_at target :: scope.openDecls } }

omit [I.Boundaryless] in
private lemma orthonormal_matrix_inverse_at
    (hb_pou : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    (coordMatrix (I := I) (M := M) g α (b := b)).transpose *
        coordMatrix (I := I) (M := M) g α (b := b) =
      chartInvGramMatrix (I := I) g α b := by
  classical
  have hAGA := orthonormal_matrix_form_at (I := I) (M := M) g α
      (b := b) hb_pou hb
  set A : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ :=
    coordMatrix (I := I) (M := M) g α (b := b)
  set G : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ := DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b
  have hAGA_right : A * (G * A.transpose) = 1 := by
    rw [← Matrix.mul_assoc]; exact hAGA
  have hG_At_eq_invA : G * A.transpose = A⁻¹ :=
    (Matrix.inv_eq_right_inv hAGA_right).symm
  have hA_left_inv : (G * A.transpose) * A = 1 :=
    mul_eq_one_comm.mp hAGA_right
  rw [Matrix.mul_assoc] at hA_left_inv
  have hAt_eq_Ginv : A.transpose * A = G⁻¹ :=
    (Matrix.inv_eq_right_inv hA_left_inv).symm
  unfold chartInvGramMatrix
  exact hAt_eq_Ginv

run_cmd do
  let target := ``Submission.DifferentialGeometry.Geometry.Connection.orthonormal_matrix_inverse_at
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Geometry.Connection.orthonormal_matrix_inverse_at target :: scope.openDecls } }

end LinearAlgebra

omit [I.Boundaryless] in
theorem chartFrameNormGlobalSmoothCoordMatrix_orthonormality
    (g : SmoothRiemannianMetric I M) (α : M)
    {b : M}
    (hb_pou : b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α)
    (k l : Fin (Module.finrank ℝ E)) :
    (∑ i : Fin (Module.finrank ℝ E),
        chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i k b *
          chartFrameNormGlobalSmoothCoordMatrix (I := I) (M := M) g α i l b) =
      chartInvGramMatrix (I := I) g α b k l := by
  classical
  have h := orthonormal_matrix_inverse_at (I := I) (M := M) g α
      (b := b) hb_pou hb
  have heval : ((coordMatrix (I := I) (M := M) g α (b := b)).transpose *
      coordMatrix (I := I) (M := M) g α (b := b)) k l =
        chartInvGramMatrix (I := I) g α b k l := by
    rw [h]
  rw [Matrix.mul_apply] at heval
  rw [show (∑ i,
        (coordMatrix (I := I) (M := M) g α (b := b)).transpose k i *
          coordMatrix (I := I) (M := M) g α (b := b) i l) =
      ∑ i,
        coordMatrix (I := I) (M := M) g α (b := b) i k *
          coordMatrix (I := I) (M := M) g α (b := b) i l from by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Matrix.transpose_apply]] at heval
  simp only [coordMatrix_apply] at heval
  exact heval

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmoothCoordMatrix_orthonormality then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmoothCoordMatrix_orthonormality"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmoothCoordMatrix_orthonormality ``Submission.DifferentialGeometry.Geometry.Connection.chartFrameNormGlobalSmoothCoordMatrix_orthonormality

end Connection
end Geometry
end DifferentialGeometry
