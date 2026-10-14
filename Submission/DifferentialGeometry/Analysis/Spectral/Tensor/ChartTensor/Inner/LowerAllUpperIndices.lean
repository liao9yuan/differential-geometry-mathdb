import Submission.DifferentialGeometry.Tensor.RSTensor.Defs
import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Bundle.SectionRegularity
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Submission.DifferentialGeometry.Geometry.Metric.PointwiseInner.DualMetric
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.FiniteDimension

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Set _root_.IsManifold _root_.ContinuousLinearMap _root_.Submission.ContinuousLinearMap _root_.Bundle.ContinuousLinearMap
open scoped _root_.Manifold _root_.Topology _root_.Bundle _root_.Submission.Bundle _root_.ContDiff _root_.BigOperators _root_.Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.L2
open _root_.Submission.DifferentialGeometry.Tensor
open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def chartCoordCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ E) => ℝ) i).comp
    (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFunL.toContinuousLinearMap

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM

@[simp]
lemma chartCoordCLM_apply (i : Fin (Module.finrank ℝ E)) (u : E) :
    chartCoordCLM E i u = (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u i := by
  unfold chartCoordCLM
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartCoordCLM_apply

def chartGramBilin (g : SmoothRiemannianMetric I M) (α b : M) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
    DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b j k • (chartCoordCLM E j).smulRight (chartCoordCLM E k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramBilin then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramBilin"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramBilin ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramBilin

@[simp]
lemma chartGramBilin_apply
    (g : SmoothRiemannianMetric I M) (α b : M) (u w : E) :
    chartGramBilin (I := I) (M := M) g α b u w =
      ∑ j : Fin (Module.finrank ℝ E), ∑ k : Fin (Module.finrank ℝ E),
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix g α b j k *
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun u j *
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun w k := by
  unfold chartGramBilin
  simp [sum_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramBilin_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramBilin_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramBilin_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramBilin_apply

def chartSeparableFormAt
    (g : SmoothRiemannianMetric I M) (α b : M) (r : ℕ) (v : Fin r → E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin r => E) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
    (fun k => chartGramBilin (I := I) (M := M) g α b (v k))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt

@[simp]
lemma chartSeparableFormAt_apply
    (g : SmoothRiemannianMetric I M) (α b : M) (r : ℕ) (v w : Fin r → E) :
    chartSeparableFormAt (I := I) (M := M) g α b r v w =
      ∏ k : Fin r,
        chartGramBilin (I := I) (M := M) g α b (v k) (w k) := by
  unfold chartSeparableFormAt
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt_apply

private lemma chartSeparableFormAt_update_add
    (g : SmoothRiemannianMetric I M) (α b : M) (r : ℕ)
    (v : Fin r → E) (i : Fin r) (a c : E) :
    chartSeparableFormAt (I := I) (M := M) g α b r
        (Function.update v i (a + c))
      = chartSeparableFormAt (I := I) (M := M) g α b r (Function.update v i a) +
        chartSeparableFormAt (I := I) (M := M) g α b r (Function.update v i c) := by
  classical
  refine ContinuousMultilinearMap.ext ?_
  intro w
  simp only [chartSeparableFormAt_apply, add_apply]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase, Function.update_self]
  have hrest : ∀ (d : E),
      ∏ k ∈ Finset.univ.erase i,
          chartGramBilin (I := I) (M := M) g α b
            (Function.update v i d k) (w k)
        = ∏ k ∈ Finset.univ.erase i,
            chartGramBilin (I := I) (M := M) g α b (v k) (w k) := by
    intro d
    refine Finset.prod_congr rfl ?_
    intro k hk
    rw [Finset.mem_erase] at hk
    rw [Function.update_of_ne hk.1]
  rw [hrest, hrest, hrest]
  have h_bilin_add :
      chartGramBilin (I := I) (M := M) g α b (a + c) (w i) =
        chartGramBilin (I := I) (M := M) g α b a (w i) +
          chartGramBilin (I := I) (M := M) g α b c (w i) := by
    rw [ContinuousLinearMap.map_add, add_apply]
  rw [h_bilin_add]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt_update_add
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt_update_add target :: scope.openDecls } }

private lemma chartSeparableFormAt_update_smul
    (g : SmoothRiemannianMetric I M) (α b : M) (r : ℕ)
    (v : Fin r → E) (i : Fin r) (c : ℝ) (a : E) :
    chartSeparableFormAt (I := I) (M := M) g α b r
        (Function.update v i (c • a))
      = c • chartSeparableFormAt (I := I) (M := M) g α b r (Function.update v i a) := by
  classical
  refine ContinuousMultilinearMap.ext ?_
  intro w
  simp only [chartSeparableFormAt_apply, smul_apply,
    smul_eq_mul]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  simp only [Finset.sdiff_singleton_eq_erase, Function.update_self]
  have hrest : ∀ (d : E),
      ∏ k ∈ Finset.univ.erase i,
          chartGramBilin (I := I) (M := M) g α b
            (Function.update v i d k) (w k)
        = ∏ k ∈ Finset.univ.erase i,
            chartGramBilin (I := I) (M := M) g α b (v k) (w k) := by
    intro d
    refine Finset.prod_congr rfl ?_
    intro k hk
    rw [Finset.mem_erase] at hk
    rw [Function.update_of_ne hk.1]
  rw [hrest, hrest]
  have h_bilin_smul :
      chartGramBilin (I := I) (M := M) g α b (c • a) (w i) =
        c * chartGramBilin (I := I) (M := M) g α b a (w i) := by
    rw [ContinuousLinearMap.map_smul, smul_apply, smul_eq_mul]
  rw [h_bilin_smul]
  ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt_update_smul
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt_update_smul target :: scope.openDecls } }

private def chartLowerAllUpperIndices_modelFn
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α b : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) : ℝ :=
  T (chartSeparableFormAt (I := I) (M := M) g α b r
      (fun i : Fin r => v (Fin.castAdd s i)))
    (fun j : Fin s => v (Fin.natAdd r j))

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_modelFn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_modelFn target :: scope.openDecls } }

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E] in
private lemma upd_castAdd_first {r s : ℕ} (v : Fin (r + s) → E) (i : Fin r) (c : E) :
    (fun k : Fin r => Function.update v (Fin.castAdd s i) c (Fin.castAdd s k)) =
      Function.update (fun k : Fin r => v (Fin.castAdd s k)) i c := by
  classical
  funext k
  rw [Function.update_apply, Function.update_apply]
  by_cases hk : k = i
  · subst hk; simp
  · rw [if_neg hk, if_neg]
    intro h
    exact hk (Fin.castAdd_injective r s h.symm).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.upd_castAdd_first
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.upd_castAdd_first target :: scope.openDecls } }

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E] in
private lemma upd_castAdd_first_noop_last
    {r s : ℕ} (v : Fin (r + s) → E) (i : Fin r) (c : E) :
    (fun j : Fin s => Function.update v (Fin.castAdd s i) c (Fin.natAdd r j)) =
      (fun j : Fin s => v (Fin.natAdd r j)) := by
  classical
  funext j
  rw [Function.update_apply]
  rw [if_neg]
  intro h
  have hcoe := Fin.val_eq_of_eq h
  simp [Fin.castAdd, Fin.natAdd] at hcoe
  omega

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.upd_castAdd_first_noop_last
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.upd_castAdd_first_noop_last target :: scope.openDecls } }

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E] in
private lemma upd_natAdd_last_noop_first
    {r s : ℕ} (v : Fin (r + s) → E) (j : Fin s) (c : E) :
    (fun k : Fin r => Function.update v (Fin.natAdd r j) c (Fin.castAdd s k)) =
      (fun k : Fin r => v (Fin.castAdd s k)) := by
  classical
  funext k
  rw [Function.update_apply]
  rw [if_neg]
  intro h
  have hcoe := Fin.val_eq_of_eq h
  simp [Fin.castAdd, Fin.natAdd] at hcoe
  omega

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.upd_natAdd_last_noop_first
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.upd_natAdd_last_noop_first target :: scope.openDecls } }

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E] in
private lemma upd_natAdd_last
    {r s : ℕ} (v : Fin (r + s) → E) (j : Fin s) (c : E) :
    (fun k : Fin s => Function.update v (Fin.natAdd r j) c (Fin.natAdd r k)) =
      Function.update (fun k : Fin s => v (Fin.natAdd r k)) j c := by
  classical
  funext k
  rw [Function.update_apply, Function.update_apply]
  by_cases hk : k = j
  · subst hk; simp
  · rw [if_neg hk, if_neg]
    intro h
    exact hk (Fin.natAdd_injective s r h.symm).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.upd_natAdd_last
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.upd_natAdd_last target :: scope.openDecls } }

private noncomputable def chartLowerAllUpperIndices_modelML
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α b : M)
    (T : TensorRSModel r s ℝ E) :
    MultilinearMap ℝ (fun _ : Fin (r + s) => E) ℝ := by
  classical
  refine MultilinearMap.mk'
    (fun v => chartLowerAllUpperIndices_modelFn (I := I) (M := M) r s g α b T v)
    (fun v i a c => ?_) (fun v i c a => ?_)
  · refine Fin.addCases ?_ ?_ i
    · intro i'
      simp only [chartLowerAllUpperIndices_modelFn]
      rw [upd_castAdd_first_noop_last,
          upd_castAdd_first_noop_last,
          upd_castAdd_first_noop_last,
          upd_castAdd_first,
          upd_castAdd_first,
          upd_castAdd_first]
      rw [chartSeparableFormAt_update_add,
          ContinuousLinearMap.map_add,
          add_apply]
    · intro j'
      simp only [chartLowerAllUpperIndices_modelFn]
      rw [upd_natAdd_last_noop_first,
          upd_natAdd_last_noop_first,
          upd_natAdd_last_noop_first,
          upd_natAdd_last,
          upd_natAdd_last,
          upd_natAdd_last]
      rw [ContinuousMultilinearMap.map_update_add]
  · refine Fin.addCases ?_ ?_ i
    · intro i'
      simp only [chartLowerAllUpperIndices_modelFn]
      rw [upd_castAdd_first_noop_last,
          upd_castAdd_first_noop_last,
          upd_castAdd_first,
          upd_castAdd_first]
      rw [chartSeparableFormAt_update_smul,
          ContinuousLinearMap.map_smul,
          smul_apply]
    · intro j'
      simp only [chartLowerAllUpperIndices_modelFn]
      rw [upd_natAdd_last_noop_first,
          upd_natAdd_last_noop_first,
          upd_natAdd_last,
          upd_natAdd_last]
      rw [ContinuousMultilinearMap.map_update_smul]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_modelML
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_modelML target :: scope.openDecls } }

@[simp]
private lemma chartLowerAllUpperIndices_modelML_apply
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α b : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) :
    chartLowerAllUpperIndices_modelML (I := I) (M := M) r s g α b T v =
      T (chartSeparableFormAt (I := I) (M := M) g α b r
          (fun i : Fin r => v (Fin.castAdd s i)))
        (fun j : Fin s => v (Fin.natAdd r j)) := by
  classical
  unfold chartLowerAllUpperIndices_modelML
  rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_modelML_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_modelML_apply target :: scope.openDecls } }

private lemma chartLowerAllUpperIndices_modelML_norm_bound
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α b : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) :
    ‖chartLowerAllUpperIndices_modelML (I := I) (M := M) r s g α b T v‖ ≤
      (‖T‖ * ∏ _i : Fin r, ‖chartGramBilin (I := I) (M := M) g α b‖) *
        ∏ k : Fin (r + s), ‖v k‖ := by
  classical
  rw [chartLowerAllUpperIndices_modelML_apply]
  have hsplit : ∏ j : Fin (r + s), ‖v j‖
      = (∏ i : Fin r, ‖v (Fin.castAdd s i)‖) *
        ∏ j : Fin s, ‖v (Fin.natAdd r j)‖ := by
    rw [Fin.prod_univ_add]
  set α' := chartSeparableFormAt (I := I) (M := M) g α b r
      (fun i : Fin r => v (Fin.castAdd s i)) with hα'_def
  have hα'_norm :
      ‖α'‖ ≤ ∏ i : Fin r, ‖chartGramBilin (I := I) (M := M) g α b‖ *
              ‖v (Fin.castAdd s i)‖ := by
    rw [hα'_def]
    unfold chartSeparableFormAt
    have h₁ :
        ‖(ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ).compContinuousLinearMap
            (fun i : Fin r =>
              chartGramBilin (I := I) (M := M) g α b (v (Fin.castAdd s i)))‖
          ≤ ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ‖ *
            ∏ i : Fin r,
              ‖chartGramBilin (I := I) (M := M) g α b (v (Fin.castAdd s i))‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    have h_mkPi : ‖ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin r) ℝ‖ = 1 :=
      ContinuousMultilinearMap.norm_mkPiAlgebra
    rw [h_mkPi, one_mul] at h₁
    refine h₁.trans ?_
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) ?_
    intro i _
    exact (chartGramBilin (I := I) (M := M) g α b).le_opNorm
      (v (Fin.castAdd s i))
  have h_step1 :
      ‖T α' (fun j : Fin s => v (Fin.natAdd r j))‖
        ≤ ‖T α'‖ * ∏ j : Fin s, ‖v (Fin.natAdd r j)‖ :=
    (T α').le_opNorm (fun j : Fin s => v (Fin.natAdd r j))
  have h_step2 :
      ‖T α'‖ * ∏ j : Fin s, ‖v (Fin.natAdd r j)‖
        ≤ (‖T‖ * ‖α'‖) * ∏ j : Fin s, ‖v (Fin.natAdd r j)‖ := by
    gcongr
    exact T.le_opNorm α'
  have h_step3 :
      (‖T‖ * ‖α'‖) * ∏ j : Fin s, ‖v (Fin.natAdd r j)‖
        ≤ (‖T‖ * (∏ i : Fin r,
              ‖chartGramBilin (I := I) (M := M) g α b‖ *
                ‖v (Fin.castAdd s i)‖)) *
            ∏ j : Fin s, ‖v (Fin.natAdd r j)‖ := by
    gcongr
  have h_step4 :
      (‖T‖ * (∏ i : Fin r,
              ‖chartGramBilin (I := I) (M := M) g α b‖ *
                ‖v (Fin.castAdd s i)‖)) *
            ∏ j : Fin s, ‖v (Fin.natAdd r j)‖
        = (‖T‖ * ∏ _i : Fin r, ‖chartGramBilin (I := I) (M := M) g α b‖) *
            ((∏ i : Fin r, ‖v (Fin.castAdd s i)‖) *
              ∏ j : Fin s, ‖v (Fin.natAdd r j)‖) := by
    rw [Finset.prod_mul_distrib]; ring
  have h_step5 :
      (‖T‖ * ∏ _i : Fin r, ‖chartGramBilin (I := I) (M := M) g α b‖) *
            ((∏ i : Fin r, ‖v (Fin.castAdd s i)‖) *
              ∏ j : Fin s, ‖v (Fin.natAdd r j)‖)
        = (‖T‖ * ∏ _i : Fin r, ‖chartGramBilin (I := I) (M := M) g α b‖) *
            ∏ j : Fin (r + s), ‖v j‖ := by
    rw [← hsplit]
  linarith [h_step1, h_step2, h_step3, h_step4, h_step5]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_modelML_norm_bound
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_modelML_norm_bound target :: scope.openDecls } }

def chartLowerAllUpperIndicesModel
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α b : M)
    (T : TensorRSModel r s ℝ E) : Tensor0SModel (r + s) ℝ E :=
  (chartLowerAllUpperIndices_modelML (I := I) (M := M) r s g α b T).mkContinuous
    (‖T‖ * ∏ _i : Fin r, ‖chartGramBilin (I := I) (M := M) g α b‖)
    (chartLowerAllUpperIndices_modelML_norm_bound (I := I) (M := M)
      r s g α b T)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndicesModel then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndicesModel"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndicesModel ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndicesModel

@[simp]
lemma chartLowerAllUpperIndices_model_apply
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α b : M)
    (T : TensorRSModel r s ℝ E) (v : Fin (r + s) → E) :
    chartLowerAllUpperIndicesModel (I := I) (M := M) r s g α b T v =
      T (chartSeparableFormAt (I := I) (M := M) g α b r
          (fun i : Fin r => v (Fin.castAdd s i)))
        (fun j : Fin s => v (Fin.natAdd r j)) := by
  unfold chartLowerAllUpperIndicesModel
  change chartLowerAllUpperIndices_modelML (I := I) (M := M)
      r s g α b T v = _
  rw [chartLowerAllUpperIndices_modelML_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_apply ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_apply

lemma chartLowerAllUpperIndices_model_zero
    (s : ℕ) (g : SmoothRiemannianMetric I M) (α b : M)
    (T : TensorRSModel 0 s ℝ E) (v : Fin (0 + s) → E) :
    chartLowerAllUpperIndicesModel (I := I) (M := M) 0 s g α b T v =
      T (ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E) (1 : ℝ))
        (fun j : Fin s => v (Fin.natAdd 0 j)) := by
  rw [chartLowerAllUpperIndices_model_apply]
  have h_empty :
      chartSeparableFormAt (I := I) (M := M) g α b 0
          (fun i : Fin 0 => v (Fin.castAdd s i))
        = ContinuousMultilinearMap.constOfIsEmpty ℝ (fun _ : Fin 0 => E)
            (1 : ℝ) := by
    refine ContinuousMultilinearMap.ext ?_
    intro w
    rw [chartSeparableFormAt_apply]
    simp
  rw [h_empty]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_zero ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_zero

lemma chartLowerAllUpperIndices_model_succ
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α b : M)
    (T : TensorRSModel (r + 1) s ℝ E) (v : Fin ((r + 1) + s) → E) :
    chartLowerAllUpperIndicesModel (I := I) (M := M) (r + 1) s g α b T v =
      T (chartSeparableFormAt (I := I) (M := M) g α b (r + 1)
          (fun i : Fin (r + 1) => v (Fin.castAdd s i)))
        (fun j : Fin s => v (Fin.natAdd (r + 1) j)) := by
  rw [chartLowerAllUpperIndices_model_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_succ then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_succ"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_succ ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_succ

lemma chartLowerAllUpperIndices_model_zero_tensor
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α b : M) :
    chartLowerAllUpperIndicesModel (I := I) (M := M) r s g α b
        (0 : TensorRSModel r s ℝ E) = 0 := by
  refine ContinuousMultilinearMap.ext ?_
  intro v
  rw [chartLowerAllUpperIndices_model_apply, zero_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_zero_tensor then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_zero_tensor"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_zero_tensor ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_zero_tensor

lemma chartLowerAllUpperIndices_model_add
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α b : M)
    (T₁ T₂ : TensorRSModel r s ℝ E) :
    chartLowerAllUpperIndicesModel (I := I) (M := M) r s g α b (T₁ + T₂) =
      chartLowerAllUpperIndicesModel (I := I) (M := M) r s g α b T₁ +
        chartLowerAllUpperIndicesModel (I := I) (M := M) r s g α b T₂ := by
  refine ContinuousMultilinearMap.ext ?_
  intro v
  simp [chartLowerAllUpperIndices_model_apply,
    add_apply, add_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_add ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_add

lemma chartLowerAllUpperIndices_model_smul
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α b : M)
    (c : ℝ) (T : TensorRSModel r s ℝ E) :
    chartLowerAllUpperIndicesModel (I := I) (M := M) r s g α b (c • T) =
      c • chartLowerAllUpperIndicesModel (I := I) (M := M) r s g α b T := by
  refine ContinuousMultilinearMap.ext ?_
  intro v
  simp [chartLowerAllUpperIndices_model_apply,
    smul_apply, smul_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_smul ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_smul

section Smoothness


private noncomputable def chartLowerEvalBasisLinear (n : ℕ) :
    Tensor0SModel n ℝ E →ₗ[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) where
  toFun := fun Φ φ => Φ (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k))
  map_add' Φ₁ Φ₂ := by
    funext φ
    simp [add_apply]
  map_smul' c Φ := by
    funext φ
    simp [smul_apply]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerEvalBasisLinear
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerEvalBasisLinear target :: scope.openDecls } }

@[simp] private lemma chartLowerEvalBasisLinear_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    chartLowerEvalBasisLinear (E := E) n Φ φ =
      Φ (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerEvalBasisLinear_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerEvalBasisLinear_apply target :: scope.openDecls } }

private lemma chartLowerEvalBasisLinear_injective (n : ℕ) :
    Function.Injective (chartLowerEvalBasisLinear (E := E) n) := by
  intro Φ₁ Φ₂ h
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  refine Module.Basis.ext_multilinear (e := fun _ : Fin n => DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) ?_
  intro v
  exact congr_fun h v

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerEvalBasisLinear_injective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerEvalBasisLinear_injective target :: scope.openDecls } }

private lemma chartLower_finrank_tensor0SModel (n : ℕ) :
    Module.finrank ℝ (Tensor0SModel n ℝ E) =
      (Module.finrank ℝ E) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero]
      rw [(continuousMultilinearCurryFin0 ℝ E ℝ).toLinearEquiv.finrank_eq]
      exact Module.finrank_self ℝ
  | succ n ih =>
      rw [(continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => E) ℝ).toLinearEquiv.finrank_eq]
      let φ : (E →L[ℝ] Tensor0SModel n ℝ E) ≃ₗ[ℝ]
          (E →ₗ[ℝ] Tensor0SModel n ℝ E) :=
        { toFun := fun f => f.toLinearMap
          invFun := fun f => LinearMap.toContinuousLinearMap f
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      rw [φ.finrank_eq, Module.finrank_linearMap, ih]
      ring

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLower_finrank_tensor0SModel
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLower_finrank_tensor0SModel target :: scope.openDecls } }

omit [Module.Finite ℝ E] in
private lemma chartLower_finrank_basis_pi (n : ℕ) :
    Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) =
      (Module.finrank ℝ E) ^ n := by
  rw [Module.finrank_pi, Fintype.card_pi]
  simp [Fintype.card_fin]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLower_finrank_basis_pi
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLower_finrank_basis_pi target :: scope.openDecls } }

private lemma chartLowerEvalBasisLinear_bijective (n : ℕ) :
    Function.Bijective (chartLowerEvalBasisLinear (E := E) n) := by
  have h_inj := chartLowerEvalBasisLinear_injective (E := E) n
  refine ⟨h_inj, ?_⟩
  have h_eq : Module.finrank ℝ (Tensor0SModel n ℝ E) =
      Module.finrank ℝ ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) := by
    rw [chartLower_finrank_tensor0SModel, chartLower_finrank_basis_pi]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_eq).mp h_inj

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerEvalBasisLinear_bijective
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerEvalBasisLinear_bijective target :: scope.openDecls } }

private noncomputable def chartLowerEvalBasisCLE (n : ℕ) :
    Tensor0SModel n ℝ E ≃L[ℝ]
      ((Fin n → Fin (Module.finrank ℝ E)) → ℝ) :=
  (LinearEquiv.ofBijective (chartLowerEvalBasisLinear (E := E) n)
    (chartLowerEvalBasisLinear_bijective (E := E) n)).toContinuousLinearEquiv

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerEvalBasisCLE
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerEvalBasisCLE target :: scope.openDecls } }

@[simp] private lemma chartLowerEvalBasisCLE_apply (n : ℕ)
    (Φ : Tensor0SModel n ℝ E)
    (φ : Fin n → Fin (Module.finrank ℝ E)) :
    chartLowerEvalBasisCLE (E := E) n Φ φ =
      Φ (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)) := rfl

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerEvalBasisCLE_apply
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerEvalBasisCLE_apply target :: scope.openDecls } }

omit [IsManifold I ∞ M] in
private lemma contMDiffOn_into_tensor0SModel_of_eval_basis_local
    {n : ℕ} {U : Set M} (Φ : M → Tensor0SModel n ℝ E)
    (h : ∀ φ : Fin n → Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun b : M =>
        Φ b (fun k : Fin n => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k))) U) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel n ℝ E) ∞ Φ U := by
  have hpi : ContMDiffOn I 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ) ∞
      (fun b : M => chartLowerEvalBasisCLE (E := E) n (Φ b)) U := by
    rw [contMDiffOn_pi_space]
    intro φ
    exact h φ
  have hsymm_smooth :
      ContMDiff 𝓘(ℝ, (Fin n → Fin (Module.finrank ℝ E)) → ℝ)
        𝓘(ℝ, Tensor0SModel n ℝ E) ∞
        (chartLowerEvalBasisCLE (E := E) n).symm :=
    (chartLowerEvalBasisCLE (E := E) n).symm.toContinuousLinearMap.contMDiff
  have hcomp := hsymm_smooth.comp_contMDiffOn hpi
  refine hcomp.congr ?_
  intro b _
  exact ((chartLowerEvalBasisCLE (E := E) n).symm_apply_apply (Φ b)).symm

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiffOn_into_tensor0SModel_of_eval_basis_local
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.contMDiffOn_into_tensor0SModel_of_eval_basis_local target :: scope.openDecls } }

private lemma chartGramBilin_basis_basis
    (g : SmoothRiemannianMetric I M) (α b : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramBilin (I := I) (M := M) g α b
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) =
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i j := by
  classical
  rw [chartGramBilin_apply]
  have hcollapse :
      ∀ j' : Fin (Module.finrank ℝ E),
        (∑ k : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b j' k *
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) j' *
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) k)
          = if j' = i then DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i j else 0 := by
    intro j'
    by_cases hj' : j' = i
    · rw [hj']
      have hself_i :
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) i = 1 := by
        rw [(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun_self]
        simp
      have hk_sum :
          (∑ k : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i k *
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) i *
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) k)
            = DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i j := by
        rw [Finset.sum_eq_single j]
        · rw [hself_i, mul_one]
          have hjj :
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) j = 1 := by
            rw [(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun_self]; simp
          rw [hjj, mul_one]
        · intro k _ hk
          have hkj_zero :
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) k = 0 := by
            rw [(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun_self]
            simp [hk.symm]
          rw [hkj_zero, _root_.MulZeroClass.mul_zero]
        · intro h
          exact (h (Finset.mem_univ _)).elim
      rw [hk_sum]
      simp
    · have hzero :
          (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) j' = 0 := by
        rw [(DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun_self]
        simp [Ne.symm hj']
      have h_sum_zero :
          (∑ k : Fin (Module.finrank ℝ E),
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b j' k *
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) j' *
                (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) k)
            = 0 := by
        refine Finset.sum_eq_zero ?_
        intro k _
        rw [hzero]; ring
      rw [h_sum_zero]
      simp [hj']
  have houter :
      (∑ j' : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b j' k *
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i) j' *
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).equivFun ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j) k)
        = ∑ j' : Fin (Module.finrank ℝ E),
            if j' = i then DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i j else 0 := by
    refine Finset.sum_congr rfl ?_
    intro j' _
    exact hcollapse j'
  rw [houter, Finset.sum_ite_eq' Finset.univ i (fun _ =>
      DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b i j)]
  simp

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramBilin_basis_basis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartGramBilin_basis_basis target :: scope.openDecls } }

private lemma chartSeparableFormAt_basis_basis
    (g : SmoothRiemannianMetric I M) (α b : M) (r : ℕ)
    (φ_first ψ : Fin r → Fin (Module.finrank ℝ E)) :
    chartSeparableFormAt (I := I) (M := M) g α b r
        (fun k : Fin r => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ_first k))
        (fun k : Fin r => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (ψ k)) =
      ∏ k : Fin r,
        DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b (φ_first k) (ψ k) := by
  rw [chartSeparableFormAt_apply]
  refine Finset.prod_congr rfl ?_
  intro k _
  exact chartGramBilin_basis_basis (I := I) (M := M) g α b
    (φ_first k) (ψ k)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt_basis_basis
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt_basis_basis target :: scope.openDecls } }

private lemma chartSeparableFormAt_basis_contMDiffOn
    {r : ℕ} (g : SmoothRiemannianMetric I M) (α : M)
    (φ_first : Fin r → Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel r ℝ E) ∞
      (fun b : M => chartSeparableFormAt (I := I) (M := M) g α b r
        (fun k : Fin r => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ_first k)))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  refine contMDiffOn_into_tensor0SModel_of_eval_basis_local _ ?_
  intro ψ
  have heq :
      (fun b : M =>
          chartSeparableFormAt (I := I) (M := M) g α b r
            (fun k : Fin r => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ_first k))
            (fun k : Fin r => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (ψ k)))
        = fun b : M =>
            ∏ k : Fin r,
              DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) g α b (φ_first k) (ψ k) := by
    funext b
    exact chartSeparableFormAt_basis_basis (I := I) (M := M) g α b r φ_first ψ
  rw [heq]
  refine contMDiffOn_finsetProd (fun k _ => ?_)
  exact DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_entry_contMDiffOn (I := I) g α (φ_first k) (ψ k)

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt_basis_contMDiffOn
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartSeparableFormAt_basis_contMDiffOn target :: scope.openDecls } }

theorem chartLowerAllUpperIndices_model_contMDiffOn
    (g : SmoothRiemannianMetric I M)
    (r s : ℕ) (α : M) (T : TensorRSModel r s ℝ E) :
    ContMDiffOn I 𝓘(ℝ, Tensor0SModel (r + s) ℝ E) ∞
      (fun b : M => chartLowerAllUpperIndicesModel
        (I := I) (M := M) r s g α b T)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
  refine contMDiffOn_into_tensor0SModel_of_eval_basis_local _ ?_
  intro φ
  set v_first : Fin r → E :=
    fun k => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ (Fin.castAdd s k)) with hv_first
  set v_last : Fin s → E :=
    fun j => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ (Fin.natAdd r j)) with hv_last
  have hrewrite :
      (fun b : M =>
          chartLowerAllUpperIndicesModel
              (I := I) (M := M) r s g α b T
            (fun k : Fin (r + s) => (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (φ k)))
        = fun b : M =>
            T (chartSeparableFormAt (I := I) (M := M) g α b r v_first) v_last := by
    funext b
    rw [chartLowerAllUpperIndices_model_apply]
  rw [hrewrite]
  let evalLast : Tensor0SModel s ℝ E →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => E) ℝ v_last
  let composed : Tensor0SModel r ℝ E →L[ℝ] ℝ := evalLast.comp T
  have hcomposed_apply : ∀ Φ : Tensor0SModel r ℝ E,
      composed Φ = T Φ v_last := by
    intro Φ; rfl
  have hΦ : ContMDiffOn I 𝓘(ℝ, Tensor0SModel r ℝ E) ∞
      (fun b : M => chartSeparableFormAt (I := I) (M := M) g α b r v_first)
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet := by
    have :=
      chartSeparableFormAt_basis_contMDiffOn (I := I) (M := M) (r := r) g α
        (fun k : Fin r => φ (Fin.castAdd s k))
    convert this using 2
  have hcomp : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
      (fun b : M => composed
        (chartSeparableFormAt (I := I) (M := M) g α b r v_first))
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
    composed.contMDiff.comp_contMDiffOn hΦ
  refine hcomp.congr ?_
  intro b _
  exact hcomposed_apply _

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_contMDiffOn ``Submission.DifferentialGeometry.Analysis.Parabolic.TensorSpectral.chartLowerAllUpperIndices_model_contMDiffOn

end Smoothness

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
