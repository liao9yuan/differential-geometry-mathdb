import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Submission.DifferentialGeometry.Tensor.Coordinates.ModelBasis
import Submission.DifferentialGeometry.Bundle.TangentSpace
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.LinearAlgebra.Matrix.ToLin

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

omit [Module.Finite ℝ E] in
lemma trivializationAt_baseSet_eq_chartAt_source (x₀ : M) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet =
      (chartAt H x₀).source :=
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.trivializationAt_baseSet_eq_chartAt_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.trivializationAt_baseSet_eq_chartAt_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.trivializationAt_baseSet_eq_chartAt_source ``Submission.DifferentialGeometry.Tensor.Coordinates.trivializationAt_baseSet_eq_chartAt_source

omit [Module.Finite ℝ E] [IsManifold I ∞ M] in
lemma extChartAt_source_eq_chartAt_source (x₀ : M) :
    (extChartAt I x₀).source = (chartAt H x₀).source := by
  rw [extChartAt_source]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source ``Submission.DifferentialGeometry.Tensor.Coordinates.extChartAt_source_eq_chartAt_source

omit [Module.Finite ℝ E] in
lemma extChartAt_symm_mem_trivializationAt_baseSet (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    (extChartAt I x₀).symm y ∈
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hsource : (extChartAt I x₀).symm y ∈ (extChartAt I x₀).source :=
    (extChartAt I x₀).map_target hy
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  exact hsource

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.extChartAt_symm_mem_trivializationAt_baseSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.extChartAt_symm_mem_trivializationAt_baseSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.extChartAt_symm_mem_trivializationAt_baseSet ``Submission.DifferentialGeometry.Tensor.Coordinates.extChartAt_symm_mem_trivializationAt_baseSet

def centeredChartTangentEquiv (x : M) : TangentSpace I x ≃L[ℝ] E :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ x
    (FiberBundle.mem_baseSet_trivializationAt' x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv ``Submission.DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv

def centeredChartTangentBasis (x : M) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
  (chartModelBasis E).map
    (centeredChartTangentEquiv (I := I) x).symm.toLinearEquiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis ``Submission.DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis

omit [Module.Finite ℝ E] in
@[simp] lemma centeredChartTangentEquiv_apply (x : M) (v : TangentSpace I x) :
    centeredChartTangentEquiv (I := I) x v =
      tangentSpaceModelContinuousLinearEquiv (I := I) x v := by
  rw [tangentSpaceModelContinuousLinearEquiv_apply]
  rw [centeredChartTangentEquiv]
  rw [Trivialization.coe_continuousLinearEquivAt_eq]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (b₀ := x) (b := x) (mem_chart_source H x)]
  exact (tangentBundleCore I M).coordChange_self (achart H x) x
    (by rw [tangentBundleCore_baseSet, coe_achart]; exact mem_chart_source H x) v

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_apply

omit [Module.Finite ℝ E] in
@[simp] lemma centeredChartTangentEquiv_symm_apply (x : M) (v : E) :
    (centeredChartTangentEquiv (I := I) x).symm v = v := by
  let vT : TangentSpace I x := v
  change (centeredChartTangentEquiv (I := I) x).symm v = vT
  apply (centeredChartTangentEquiv (I := I) x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  have hv : centeredChartTangentEquiv (I := I) x vT = v := by
    rw [centeredChartTangentEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_apply]
  exact hv.symm

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.centeredChartTangentEquiv_symm_apply

@[simp] lemma centeredChartTangentBasis_apply (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    centeredChartTangentBasis (I := I) x i =
      (centeredChartTangentEquiv (I := I) x).symm (chartModelBasis E i) := by
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_apply

lemma tangent_model_equiv_centered_chart_basis (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    tangentSpaceModelContinuousLinearEquiv (I := I) x
        (centeredChartTangentBasis (I := I) x i) =
      chartModelBasis E i := by
  calc
    tangentSpaceModelContinuousLinearEquiv (I := I) x
        (centeredChartTangentBasis (I := I) x i) =
      centeredChartTangentEquiv (I := I) x
        (centeredChartTangentBasis (I := I) x i) := by
          exact (centeredChartTangentEquiv_apply (I := I) x _).symm
    _ = chartModelBasis E i := by
      rw [centeredChartTangentBasis_apply, ContinuousLinearEquiv.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tangent_model_equiv_centered_chart_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tangent_model_equiv_centered_chart_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tangent_model_equiv_centered_chart_basis ``Submission.DifferentialGeometry.Tensor.Coordinates.tangent_model_equiv_centered_chart_basis

lemma tangent_model_equiv_symm_chart_basis (x : M)
    (i : Fin (Module.finrank ℝ E)) :
    (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
        (chartModelBasis E i) =
      centeredChartTangentBasis (I := I) x i := by
  apply (tangentSpaceModelContinuousLinearEquiv (I := I) x).injective
  rw [ContinuousLinearEquiv.apply_symm_apply,
    tangent_model_equiv_centered_chart_basis]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.tangent_model_equiv_symm_chart_basis then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.tangent_model_equiv_symm_chart_basis"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.tangent_model_equiv_symm_chart_basis ``Submission.DifferentialGeometry.Tensor.Coordinates.tangent_model_equiv_symm_chart_basis

@[simp] lemma centeredChartTangentBasis_repr (x : M) (v : TangentSpace I x) :
    (centeredChartTangentBasis (I := I) x).repr v =
      (chartModelBasis E).repr (centeredChartTangentEquiv (I := I) x v) := by
  simp only [centeredChartTangentBasis, Module.Basis.map_repr,
    LinearEquiv.trans_apply, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
    ContinuousLinearEquiv.symm_symm]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_repr then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_repr"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_repr ``Submission.DifferentialGeometry.Tensor.Coordinates.centeredChartTangentBasis_repr

def chartBasisVecFiber (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    TangentSpace I x :=
  (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symmL ℝ x ((chartModelBasis E) i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber ``Submission.DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber

theorem localFrame_eq_chartBasisVec
    (alpha : M) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) alpha).baseSet)
    (i : Fin (Module.finrank Real E)) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) alpha).localFrame
        (chartModelBasis E) i x =
      chartBasisVecFiber (I := I) alpha i x := by
  rw [(_root_.FiberBundle.trivializationAt E (TangentSpace I) alpha).localFrame_apply_of_mem_baseSet
    (chartModelBasis E) hx]
  rw [Bundle.Trivialization.basisAt, Module.Basis.map_apply]
  change ((_root_.FiberBundle.trivializationAt E (TangentSpace I) alpha).linearEquivAt Real x hx).symm
      (chartModelBasis E i) =
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) alpha).symmL Real x (chartModelBasis E i)
  rw [(_root_.FiberBundle.trivializationAt E (TangentSpace I) alpha).symmL_apply hx]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.localFrame_eq_chartBasisVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.localFrame_eq_chartBasisVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.localFrame_eq_chartBasisVec ``Submission.DifferentialGeometry.Tensor.Coordinates.localFrame_eq_chartBasisVec

def chartBasisVec (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    M → _root_.Bundle.TotalSpace E (TangentSpace I : M → Type _) :=
  fun x => TotalSpace.mk' E x (chartBasisVecFiber (I := I) x₀ i x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartBasisVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartBasisVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartBasisVec ``Submission.DifferentialGeometry.Tensor.Coordinates.chartBasisVec

@[simp] lemma chartBasisVec_proj (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    (chartBasisVec (I := I) x₀ i x).proj = x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartBasisVec_proj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartBasisVec_proj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartBasisVec_proj ``Submission.DifferentialGeometry.Tensor.Coordinates.chartBasisVec_proj

@[simp] lemma chartBasisVec_snd (x₀ : M) (i : Fin (Module.finrank ℝ E)) (x : M) :
    (chartBasisVec (I := I) x₀ i x).2 = chartBasisVecFiber (I := I) x₀ i x := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartBasisVec_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartBasisVec_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartBasisVec_snd ``Submission.DifferentialGeometry.Tensor.Coordinates.chartBasisVec_snd

lemma trivializationAt_chartBasisVec_snd
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) :
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀
        ⟨x, chartBasisVecFiber (I := I) x₀ i x⟩).2
      = (chartModelBasis E) i := by
  have h := (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).apply_mk_symm hx
    ((chartModelBasis E) i)
  rw [chartBasisVecFiber, Trivialization.symmL_apply _ hx]
  exact congrArg Prod.snd h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.trivializationAt_chartBasisVec_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.trivializationAt_chartBasisVec_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.trivializationAt_chartBasisVec_snd ``Submission.DifferentialGeometry.Tensor.Coordinates.trivializationAt_chartBasisVec_snd

lemma chartBasisVec_contMDiffOn
    (x₀ : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (chartBasisVec (I := I) x₀ i)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet := by
  have hiff :=
    ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀)).contMDiffOn_section_baseSet_iff
      (IB := I) (n := ∞) (s := fun x => chartBasisVecFiber (I := I) x₀ i x)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun _ : M => (chartModelBasis E) i)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro x hx
  exact (trivializationAt_chartBasisVec_snd (I := I) x₀ i hx)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn ``Submission.DifferentialGeometry.Tensor.Coordinates.chartBasisVec_contMDiffOn

lemma chartAlphaFrame_section_contMDiffOn
    (α : M) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I I.tangent ∞
      (fun b : M => TotalSpace.mk' E b
        ((_root_.FiberBundle.trivializationAt E (TangentSpace I) α).symmL ℝ b
          (chartModelBasis E i)))
      (chartAt H α).source := by
  have h_baseSet :
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    TangentBundle.trivializationAt_baseSet (I := I) α
  rw [← h_baseSet]
  refine (chartBasisVec_contMDiffOn (I := I) α i).congr ?_
  intro b hb
  simp only [chartBasisVec, chartBasisVecFiber,
    Trivialization.symmL_apply _ hb]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartAlphaFrame_section_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartAlphaFrame_section_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartAlphaFrame_section_contMDiffOn ``Submission.DifferentialGeometry.Tensor.Coordinates.chartAlphaFrame_section_contMDiffOn

def chartBasisFamily (x₀ : M) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) :
    Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
  (chartModelBasis E).map
    (ContinuousLinearEquiv.toLinearEquiv
      ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x hx).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartBasisFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartBasisFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartBasisFamily ``Submission.DifferentialGeometry.Tensor.Coordinates.chartBasisFamily

lemma chartBasisFamily_apply (x₀ : M) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisFamily (I := I) x₀ hx i =
      chartBasisVecFiber (I := I) x₀ i x := by
  unfold chartBasisFamily chartBasisVecFiber
  rw [Module.Basis.map_apply]
  exact congrFun ((_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).symm_continuousLinearEquivAt_eq hx)
    ((chartModelBasis E) i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply ``Submission.DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_apply

lemma chartBasisFamily_linearIndependent (x₀ : M) {x : M}
    (hx : x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) x₀).baseSet) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ E) =>
        chartBasisVecFiber (I := I) x₀ i x) := by
  have h := (chartBasisFamily (I := I) x₀ hx).linearIndependent
  have hcongr : (chartBasisFamily (I := I) x₀ hx : Fin (Module.finrank ℝ E) → TangentSpace I x)
      = fun i => chartBasisVecFiber (I := I) x₀ i x := by
    funext i
    exact chartBasisFamily_apply (I := I) x₀ hx i
  rw [← hcongr]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_linearIndependent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_linearIndependent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_linearIndependent ``Submission.DifferentialGeometry.Tensor.Coordinates.chartBasisFamily_linearIndependent

theorem mfderiv_chartModelBasis_eq_sum
    (f : E → M) {x : E} (hf : MDifferentiableAt (modelWithCornersSelf ℝ E) I f x)
    (y₀ : M) (hy : f x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) y₀).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) i) =
      ∑ k, (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
            (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).toLinearMap) k i •
        chartBasisVecFiber (I := I) y₀ k (f x) := by
  have hy_chart : f x ∈ (chartAt H y₀).source := by
    simpa only [trivializationAt_baseSet_eq_chartAt_source (I := I)] using hy
  have hchart : MDifferentiableAt I (modelWithCornersSelf ℝ E) (extChartAt I y₀) (f x) :=
    mdifferentiableAt_extChartAt (I := I) (x := y₀) (y := f x) hy_chart
  have hchain :
      fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x =
        (mfderiv I (modelWithCornersSelf ℝ E) (extChartAt I y₀) (f x)).comp
          (mfderiv (modelWithCornersSelf ℝ E) I f x) := by
    have hchain' := mfderiv_comp (I := (modelWithCornersSelf ℝ E)) (I' := I) (I'' := (modelWithCornersSelf ℝ E))
      (g := extChartAt I y₀) (f := f) (x := x) hchart hf
    rw [mfderiv_eq_fderiv] at hchain'
    exact hchain'
  let T₀ : _root_.Bundle.Trivialization E (π E (TangentSpace I : M → Type _)) :=
    _root_.FiberBundle.trivializationAt E (TangentSpace I) y₀
  apply (T₀.continuousLinearEquivAt ℝ (f x) hy).injective
  have hrepr :
      (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x) ((chartModelBasis E) i) =
        ∑ k, (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
              (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).toLinearMap) k i •
          (chartModelBasis E) k := by
    simp only [LinearMap.toMatrix_apply]
    exact
      (((chartModelBasis E).sum_repr
        ((fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x)
          ((chartModelBasis E) i))).symm)
  calc
    T₀.continuousLinearEquivAt ℝ (f x) hy
        (mfderiv (modelWithCornersSelf ℝ E) I f x ((chartModelBasis E) i))
        = (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x)
            ((chartModelBasis E) i) := by
          rw [Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) T₀ hy]
          rw [TangentBundle.continuousLinearMapAt_trivializationAt
            (I := I) (x₀ := y₀) (x := f x) hy_chart]
          rw [hchain]
          rfl
    _ = ∑ k, (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
          (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).toLinearMap) k i •
            (chartModelBasis E) k := hrepr
    _ = T₀.continuousLinearEquivAt ℝ (f x) hy
          (∑ k, (LinearMap.toMatrix (chartModelBasis E) (chartModelBasis E)
              (fderiv ℝ (fun z : E => extChartAt I y₀ (f z)) x).toLinearMap) k i •
            chartBasisVecFiber (I := I) y₀ k (f x)) := by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [map_smul]
          have hbasis :
              chartBasisVecFiber (I := I) y₀ k (f x) =
                (T₀.continuousLinearEquivAt ℝ (f x) hy).symm
                  ((chartModelBasis E) k) := by
            unfold chartBasisVecFiber
            exact (congrFun (T₀.symm_continuousLinearEquivAt_eq hy)
              ((chartModelBasis E) k)).symm
          rw [hbasis, ContinuousLinearEquiv.apply_symm_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.mfderiv_chartModelBasis_eq_sum then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.mfderiv_chartModelBasis_eq_sum"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.mfderiv_chartModelBasis_eq_sum ``Submission.DifferentialGeometry.Tensor.Coordinates.mfderiv_chartModelBasis_eq_sum

end DifferentialGeometry.Tensor.Coordinates
