import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Submission.DifferentialGeometry.Geometry.Connection.ChartFrame.ChartMetric
import Submission.DifferentialGeometry.Geometry.Connection.ChartFrame.ChartSection

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Operator


noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry
namespace Geometry
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem

def chartLeviCivitaGoodSet (α : M) : Set M :=
  (extChartAt I α).source ∩
    (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet ∩
    (extChartAt I α) ⁻¹' interior ((extChartAt I α).target : Set E)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet

omit [FiniteDimensional ℝ E] in
lemma chartLeviCivitaGoodSet_isOpen (α : M) :
    IsOpen (chartLeviCivitaGoodSet (I := I) α) := by
  classical
  set S₁ : Set M := (extChartAt I α).source
  set S₂ : Set M := (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet
  set S₃ : Set M :=
    (extChartAt I α) ⁻¹' interior ((extChartAt I α).target : Set E)
  have hS₁ : IsOpen S₁ := isOpen_extChartAt_source α
  have hS₂ : IsOpen S₂ := (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).open_baseSet
  have hcap_open : IsOpen (S₁ ∩ S₃) := by
    have hcont : ContinuousOn (extChartAt I α) S₁ := continuousOn_extChartAt α
    have hopen_int : IsOpen (interior ((extChartAt I α).target : Set E)) :=
      isOpen_interior
    have hpre :
        S₁ ∩ S₃ =
          S₁ ∩ (extChartAt I α) ⁻¹' interior ((extChartAt I α).target : Set E) := rfl
    rw [hpre]
    exact hcont.isOpen_inter_preimage hS₁ hopen_int
  have heq : chartLeviCivitaGoodSet (I := I) α = (S₁ ∩ S₃) ∩ S₂ := by
    ext x
    simp only [chartLeviCivitaGoodSet, S₁, S₂, S₃, Set.mem_inter_iff]
    tauto
  rw [heq]
  exact hcap_open.inter hS₂

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_isOpen then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_isOpen"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_isOpen ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_isOpen

omit [FiniteDimensional ℝ E] in
lemma mem_chartLeviCivitaGoodSet_iff {α x : M} :
    x ∈ chartLeviCivitaGoodSet (I := I) α ↔
      x ∈ (extChartAt I α).source ∧
        x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet ∧
        extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) := by
  unfold chartLeviCivitaGoodSet
  rw [Set.mem_inter_iff, Set.mem_inter_iff, and_assoc]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mem_chartLeviCivitaGoodSet_iff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mem_chartLeviCivitaGoodSet_iff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mem_chartLeviCivitaGoodSet_iff ``Submission.DifferentialGeometry.Geometry.Connection.mem_chartLeviCivitaGoodSet_iff

omit [FiniteDimensional ℝ E] in
lemma chartLeviCivitaGoodSet_mem_extChartAt_source {α x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    x ∈ (extChartAt I α).source :=
  ((mem_chartLeviCivitaGoodSet_iff.mp hx)).1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_mem_extChartAt_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_mem_extChartAt_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_mem_extChartAt_source ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_mem_extChartAt_source

omit [FiniteDimensional ℝ E] in
lemma chartLeviCivitaGoodSet_mem_chartAt_source {α x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    x ∈ (chartAt H α).source := by
  have := chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  simpa using this

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_mem_chartAt_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_mem_chartAt_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_mem_chartAt_source ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_mem_chartAt_source

omit [FiniteDimensional ℝ E] in
lemma chartLeviCivitaGoodSet_mem_baseSet {α x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    x ∈ (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet :=
  ((mem_chartLeviCivitaGoodSet_iff.mp hx)).2.1

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_mem_baseSet then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_mem_baseSet"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_mem_baseSet ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_mem_baseSet

omit [FiniteDimensional ℝ E] in
lemma chartLeviCivitaGoodSet_extChartAt_mem_interior {α x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
  ((mem_chartLeviCivitaGoodSet_iff.mp hx)).2.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_extChartAt_mem_interior then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_extChartAt_mem_interior"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_extChartAt_mem_interior ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_extChartAt_mem_interior

omit [FiniteDimensional ℝ E] in
theorem chartLeviCivitaGoodSet_eq_extChartAt_source
    [I.Boundaryless] (α : M) :
    chartLeviCivitaGoodSet (I := I) α = (extChartAt I α).source := by
  classical
  have hbase :
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) α
  have hbase_extSource :
      (_root_.FiberBundle.trivializationAt E (TangentSpace I) α).baseSet = (extChartAt I α).source := by
    rw [hbase, extChartAt_source_eq_chartAt_source (I := I)]
  have h_target_open : IsOpen ((extChartAt I α).target : Set E) :=
    isOpen_extChartAt_target (I := I) α
  have h_interior_eq :
      interior ((extChartAt I α).target : Set E) = (extChartAt I α).target :=
    h_target_open.interior_eq
  apply Set.eq_of_subset_of_subset
  · intro x hx
    exact chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
  · intro x hx
    refine (mem_chartLeviCivitaGoodSet_iff (I := I)).mpr ?_
    refine ⟨hx, ?_, ?_⟩
    · rw [hbase_extSource]
      exact hx
    · have h_map : extChartAt I α x ∈ (extChartAt I α).target :=
        (extChartAt I α).map_source hx
      rw [h_interior_eq]
      exact h_map

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_eq_extChartAt_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_eq_extChartAt_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_eq_extChartAt_source ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_eq_extChartAt_source

omit [FiniteDimensional ℝ E] in
theorem mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source
    [I.Boundaryless] (α x : M) :
    x ∈ chartLeviCivitaGoodSet (I := I) α ↔ x ∈ (extChartAt I α).source := by
  rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source ``Submission.DifferentialGeometry.Geometry.Connection.mem_chartLeviCivitaGoodSet_iff_mem_extChartAt_source

def christoffelCorrection (g : SmoothRiemannianMetric I M)
    (α : M) (x : M) (Y : E) :
    TangentSpace I x →L[ℝ] E :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap.comp
            (trivToE (I := I) α x)).smulRight
          (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr Y j *
              chartChristoffel (I := I) g α i j k (extChartAt I α x)) •
            (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.christoffelCorrection then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.christoffelCorrection"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.christoffelCorrection ``Submission.DifferentialGeometry.Geometry.Connection.christoffelCorrection

lemma christoffelCorrection_apply
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) (Y : E)
    (v : TangentSpace I x) :
    christoffelCorrection (I := I) g α x Y v =
      ∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α x v)) i *
                ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr Y) j *
                chartChristoffel (I := I) g α i j k (extChartAt I α x)) •
              (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) k := by
  classical
  unfold christoffelCorrection
  rw [sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [sum_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [sum_apply]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply]
  rw [ContinuousLinearMap.comp_apply]
  have hcoord : ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).coord i).toContinuousLinearMap
      (trivToE (I := I) α x v) =
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α x v)) i := by
    rfl
  rw [hcoord]
  rw [smul_smul, ← mul_assoc]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.christoffelCorrection_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.christoffelCorrection_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.christoffelCorrection_apply ``Submission.DifferentialGeometry.Geometry.Connection.christoffelCorrection_apply

lemma christoffelCorrection_add
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) (Y Y' : E)
    (v : TangentSpace I x) :
    christoffelCorrection (I := I) g α x (Y + Y') v =
      christoffelCorrection (I := I) g α x Y v +
        christoffelCorrection (I := I) g α x Y' v := by
  classical
  rw [christoffelCorrection_apply, christoffelCorrection_apply,
      christoffelCorrection_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hrepr : ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (Y + Y')) j =
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr Y) j +
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr Y') j := by
    rw [map_add]; rfl
  rw [hrepr]
  rw [show ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α x v)) i *
        (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr Y) j + ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr Y') j) *
        chartChristoffel (I := I) g α i j k (extChartAt I α x) =
      ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α x v)) i *
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr Y) j *
          chartChristoffel (I := I) g α i j k (extChartAt I α x) +
        ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α x v)) i *
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr Y') j *
          chartChristoffel (I := I) g α i j k (extChartAt I α x) by ring]
  rw [add_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.christoffelCorrection_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.christoffelCorrection_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.christoffelCorrection_add ``Submission.DifferentialGeometry.Geometry.Connection.christoffelCorrection_add

lemma christoffelCorrection_smul
    (g : SmoothRiemannianMetric I M) (α : M) (x : M) (c : ℝ) (Y : E)
    (v : TangentSpace I x) :
    christoffelCorrection (I := I) g α x (c • Y) v =
      c • christoffelCorrection (I := I) g α x Y v := by
  classical
  rw [christoffelCorrection_apply, christoffelCorrection_apply]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hrepr : ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (c • Y)) j =
      c * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr Y) j := by
    rw [map_smul]; rfl
  rw [hrepr]
  rw [show ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α x v)) i *
        (c * ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr Y) j) *
        chartChristoffel (I := I) g α i j k (extChartAt I α x) =
      c * (((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr (trivToE (I := I) α x v)) i *
          ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E).repr Y) j *
          chartChristoffel (I := I) g α i j k (extChartAt I α x)) by ring]
  rw [← smul_smul]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.christoffelCorrection_smul then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.christoffelCorrection_smul"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.christoffelCorrection_smul ``Submission.DifferentialGeometry.Geometry.Connection.christoffelCorrection_smul

def chartLeviCivitaInnerCLM (g : SmoothRiemannianMetric I M)
    (α : M) (σ : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] E :=
  (fderiv ℝ (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
      (extChartAt I α x)).comp (trivToE (I := I) α x) +
  christoffelCorrection (I := I) g α x (chartESectionRepr (I := I) α σ x)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivitaInnerCLM then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivitaInnerCLM"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivitaInnerCLM ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivitaInnerCLM

lemma chartLeviCivitaInnerCLM_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (σ : Π x : M, TangentSpace I x) (x : M) (v : TangentSpace I x) :
    chartLeviCivitaInnerCLM (I := I) g α σ x v =
      fderiv ℝ (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
          (extChartAt I α x) (trivToE (I := I) α x v) +
        christoffelCorrection (I := I) g α x
          (chartESectionRepr (I := I) α σ x) v := by
  classical
  unfold chartLeviCivitaInnerCLM
  rw [add_apply, ContinuousLinearMap.comp_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivitaInnerCLM_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivitaInnerCLM_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivitaInnerCLM_apply ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivitaInnerCLM_apply

open scoped _root_.Classical in
def chartLeviCivita (g : SmoothRiemannianMetric I M) (α : M) :
    (Π x : M, TangentSpace I x) →
      (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) :=
  fun σ x =>
    if x ∈ chartLeviCivitaGoodSet (I := I) α then
      (trivFromE (I := I) α x).comp
        (chartLeviCivitaInnerCLM (I := I) g α σ x)
    else 0

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivita then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivita"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivita ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivita

lemma chartLeviCivita_eq_of_mem (g : SmoothRiemannianMetric I M) (α : M)
    (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartLeviCivita (I := I) g α σ x =
      (trivFromE (I := I) α x).comp
        (chartLeviCivitaInnerCLM (I := I) g α σ x) := by
  classical
  simp only [chartLeviCivita, if_pos hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivita_eq_of_mem then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivita_eq_of_mem"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivita_eq_of_mem ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivita_eq_of_mem

lemma chartLeviCivita_apply (g : SmoothRiemannianMetric I M)
    (α : M) (σ : Π x : M, TangentSpace I x) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) (v : TangentSpace I x) :
    chartLeviCivita (I := I) g α σ x v =
      trivFromE (I := I) α x
        (fderiv ℝ (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x v) +
          christoffelCorrection (I := I) g α x
            (chartESectionRepr (I := I) α σ x) v) := by
  classical
  rw [chartLeviCivita_eq_of_mem (I := I) g α σ hx]
  rw [ContinuousLinearMap.comp_apply]
  rw [chartLeviCivitaInnerCLM_apply]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivita_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivita_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivita_apply ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivita_apply

omit [FiniteDimensional ℝ E] in
lemma differentiableAt_chartE_pullback_of_MDiff
    (α : M) {σ : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α)
    (hσ : MDiffAt (T% σ) x) :
    DifferentiableAt ℝ
      (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
      (extChartAt I α x) :=
  (mdifferentiableAt_section_iff_chartE_fderiv (I := I) α σ
    (chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx)
    (chartLeviCivitaGoodSet_mem_baseSet (I := I) hx)
    (chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx)).mp hσ

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.differentiableAt_chartE_pullback_of_MDiff then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.differentiableAt_chartE_pullback_of_MDiff"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.differentiableAt_chartE_pullback_of_MDiff ``Submission.DifferentialGeometry.Geometry.Connection.differentiableAt_chartE_pullback_of_MDiff

lemma chartLeviCivita_add (g : SmoothRiemannianMetric I M) (α : M)
    {σ σ' : Π x : M, TangentSpace I x} {x : M}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartLeviCivita (I := I) g α (σ + σ') x =
      chartLeviCivita (I := I) g α σ x + chartLeviCivita (I := I) g α σ' x := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  rw [chartLeviCivita_apply (I := I) g α (σ + σ') hx v]
  rw [add_apply,
      chartLeviCivita_apply (I := I) g α σ hx v,
      chartLeviCivita_apply (I := I) g α σ' hx v]
  rw [← map_add]
  congr 1
  have hsum_pull :
      (chartESectionRepr (I := I) α (σ + σ') ∘ (extChartAt I α).symm) =
        (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm) +
          (chartESectionRepr (I := I) α σ' ∘ (extChartAt I α).symm) := by
    funext y
    change chartESectionRepr (I := I) α (σ + σ') ((extChartAt I α).symm y) =
      chartESectionRepr (I := I) α σ ((extChartAt I α).symm y) +
        chartESectionRepr (I := I) α σ' ((extChartAt I α).symm y)
    exact chartE_section_repr_add (I := I) α σ σ' ((extChartAt I α).symm y)
  have hdiff_σ : DifferentiableAt ℝ
      (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
      (extChartAt I α x) :=
    differentiableAt_chartE_pullback_of_MDiff (I := I) α hx hσ
  have hdiff_σ' : DifferentiableAt ℝ
      (chartESectionRepr (I := I) α σ' ∘ (extChartAt I α).symm)
      (extChartAt I α x) :=
    differentiableAt_chartE_pullback_of_MDiff (I := I) α hx hσ'
  have hfderiv_split :
      fderiv ℝ
          (chartESectionRepr (I := I) α (σ + σ') ∘ (extChartAt I α).symm)
          (extChartAt I α x) =
        fderiv ℝ
            (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
            (extChartAt I α x) +
          fderiv ℝ
              (chartESectionRepr (I := I) α σ' ∘ (extChartAt I α).symm)
              (extChartAt I α x) := by
    rw [hsum_pull]
    exact fderiv_add hdiff_σ hdiff_σ'
  have hsec_add :
      chartESectionRepr (I := I) α (σ + σ') x =
        chartESectionRepr (I := I) α σ x +
          chartESectionRepr (I := I) α σ' x :=
    chartE_section_repr_add (I := I) α σ σ' x
  rw [hfderiv_split]
  rw [hsec_add]
  rw [christoffelCorrection_add (I := I) g α x
        (chartESectionRepr (I := I) α σ x)
        (chartESectionRepr (I := I) α σ' x) v]
  rw [add_apply]
  abel

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivita_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivita_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivita_add ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivita_add

lemma chartLeviCivita_leibniz (g : SmoothRiemannianMetric I M) (α : M)
    {σ : Π x : M, TangentSpace I x} {f : M → ℝ} {x : M}
    (hσ : MDiffAt (T% σ) x) (hf : MDiffAt f x)
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartLeviCivita (I := I) g α (f • σ) x =
      f x • chartLeviCivita (I := I) g α σ x +
        (mvfderiv (I := I) f x).smulRight (σ x) := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  rw [chartLeviCivita_apply (I := I) g α (f • σ) hx v]
  rw [add_apply, smul_apply,
      chartLeviCivita_apply (I := I) g α σ hx v,
      ContinuousLinearMap.smulRight_apply]
  have hsmul_pull :
      (chartESectionRepr (I := I) α (f • σ) ∘ (extChartAt I α).symm) =
        ((f ∘ (extChartAt I α).symm) •
          (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)) := by
    funext y
    have heq :
        chartESectionRepr (I := I) α (f • σ) ((extChartAt I α).symm y) =
          f ((extChartAt I α).symm y) •
            chartESectionRepr (I := I) α σ ((extChartAt I α).symm y) := by
      have hpt :
          chartESectionRepr (I := I) α
              (fun z => f z • σ z)
              ((extChartAt I α).symm y) =
            f ((extChartAt I α).symm y) •
              chartESectionRepr (I := I) α σ ((extChartAt I α).symm y) :=
        chartE_section_repr_smul_function (I := I) α f σ
          ((extChartAt I α).symm y)
      exact hpt
    change chartESectionRepr (I := I) α (f • σ) ((extChartAt I α).symm y) =
      f ((extChartAt I α).symm y) •
        chartESectionRepr (I := I) α σ ((extChartAt I α).symm y)
    exact heq
  have hdiff_σ : DifferentiableAt ℝ
      (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
      (extChartAt I α x) :=
    differentiableAt_chartE_pullback_of_MDiff (I := I) α hx hσ
  have hdiff_f : DifferentiableAt ℝ (f ∘ (extChartAt I α).symm)
      (extChartAt I α x) := by
    have hxsrc : x ∈ (extChartAt I α).source := by
      have := chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
      simpa using this
    have hxφ_inv : (extChartAt I α).symm (extChartAt I α x) = x :=
      (extChartAt I α).left_inv hxsrc
    have hxφ_target : extChartAt I α x ∈ (extChartAt I α).target :=
      (extChartAt I α).map_source hxsrc
    have hsymm_within :
        MDifferentiableWithinAt 𝓘(ℝ, E) I (extChartAt I α).symm
          (_root_.Set.range I) (extChartAt I α x) :=
      mdifferentiableWithinAt_extChartAt_symm (I := I) (x := α) hxφ_target
    have hint_open : IsOpen (interior ((extChartAt I α).target : Set E)) :=
      isOpen_interior
    have hxint :
        extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
      chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
    have hrange_nhds : _root_.Set.range I ∈ 𝓝 (extChartAt I α x) := by
      exact Filter.mem_of_superset
        (Filter.mem_of_superset (hint_open.mem_nhds hxint) interior_subset)
        (extChartAt_target_subset_range α)
    have hf_within :
        MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ) (f ∘ (extChartAt I α).symm)
          (_root_.Set.range I) (extChartAt I α x) :=
      MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq
        (I' := I) (I'' := 𝓘(ℝ)) (g := f) (f := (extChartAt I α).symm)
        (s := _root_.Set.range I) (x := extChartAt I α x) (y := x)
        hf hsymm_within hxφ_inv
    have hf_at : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ) (f ∘ (extChartAt I α).symm)
        (extChartAt I α x) :=
      hf_within.mdifferentiableAt hrange_nhds
    exact hf_at.differentiableAt
  have hfderiv_split :
      fderiv ℝ
          (chartESectionRepr (I := I) α (f • σ) ∘ (extChartAt I α).symm)
          (extChartAt I α x) =
        (f ∘ (extChartAt I α).symm) (extChartAt I α x) •
            fderiv ℝ
              (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
              (extChartAt I α x) +
          (fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)).smulRight
            ((chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
                (extChartAt I α x)) := by
    rw [hsmul_pull]
    exact fderiv_smul hdiff_f hdiff_σ
  have hxsrc : x ∈ (extChartAt I α).source := by
    have := chartLeviCivitaGoodSet_mem_extChartAt_source (I := I) hx
    simpa using this
  have hxφ_inv : (extChartAt I α).symm (extChartAt I α x) = x :=
    (extChartAt I α).left_inv hxsrc
  have hfφ : (f ∘ (extChartAt I α).symm) (extChartAt I α x) = f x := by
    change f ((extChartAt I α).symm (extChartAt I α x)) = f x
    rw [hxφ_inv]
  have hσφ : (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
        (extChartAt I α x) = chartESectionRepr (I := I) α σ x := by
    change chartESectionRepr (I := I) α σ
        ((extChartAt I α).symm (extChartAt I α x)) =
      chartESectionRepr (I := I) α σ x
    rw [hxφ_inv]
  rw [hfφ, hσφ] at hfderiv_split
  have hLfd_apply :
      fderiv ℝ
          (chartESectionRepr (I := I) α (f • σ) ∘ (extChartAt I α).symm)
          (extChartAt I α x) (trivToE (I := I) α x v) =
        f x • fderiv ℝ
            (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
            (extChartAt I α x) (trivToE (I := I) α x v) +
          fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)
              (trivToE (I := I) α x v) •
            chartESectionRepr (I := I) α σ x := by
    rw [hfderiv_split]
    rw [add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply]
  have hsec_smul :
      chartESectionRepr (I := I) α (f • σ) x =
        f x • chartESectionRepr (I := I) α σ x :=
    chartE_section_repr_smul_function (I := I) α f σ x
  have hChristoffel_lhs :
      christoffelCorrection (I := I) g α x
          (chartESectionRepr (I := I) α (f • σ) x) v =
        f x • christoffelCorrection (I := I) g α x
            (chartESectionRepr (I := I) α σ x) v := by
    rw [hsec_smul, christoffelCorrection_smul]
  have hxsrc_chart : x ∈ (chartAt H α).source :=
    chartLeviCivitaGoodSet_mem_chartAt_source (I := I) hx
  have hxint :
      extChartAt I α x ∈ interior ((extChartAt I α).target : Set E) :=
    chartLeviCivitaGoodSet_extChartAt_mem_interior (I := I) hx
  have hmf_to_fderiv :
      (mfderiv I 𝓘(ℝ) f x) v =
        fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)
          (trivToE (I := I) α x v) :=
    mfderiv_scalar_eq_chart_fderiv (I := I) α f hxsrc_chart hxint hf v
  have hextDeriv :
      mvfderiv (I := I) f x v = (mfderiv I 𝓘(ℝ) f x) v := rfl
  rw [hLfd_apply, hChristoffel_lhs]
  have hreorg :
      (f x • fderiv ℝ (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
          (extChartAt I α x) (trivToE (I := I) α x v) +
        fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)
          (trivToE (I := I) α x v) • chartESectionRepr (I := I) α σ x) +
      f x • christoffelCorrection (I := I) g α x
              (chartESectionRepr (I := I) α σ x) v =
      f x • (fderiv ℝ (chartESectionRepr (I := I) α σ ∘ (extChartAt I α).symm)
          (extChartAt I α x) (trivToE (I := I) α x v) +
          christoffelCorrection (I := I) g α x
              (chartESectionRepr (I := I) α σ x) v) +
      fderiv ℝ (f ∘ (extChartAt I α).symm) (extChartAt I α x)
        (trivToE (I := I) α x v) • chartESectionRepr (I := I) α σ x := by
    rw [smul_add]; abel
  rw [hreorg]
  rw [map_add, map_smul, map_smul]
  congr 1
  have htriv_round :
      trivFromE (I := I) α x (chartESectionRepr (I := I) α σ x) = σ x := by
    rw [chartE_section_repr_eq_trivToE]
    exact trivFromE_trivToE (I := I) α
      (chartLeviCivitaGoodSet_mem_baseSet (I := I) hx) (σ x)
  rw [htriv_round]
  rw [← hmf_to_fderiv, ← hextDeriv]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivita_leibniz then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivita_leibniz"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivita_leibniz ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivita_leibniz

theorem chartLeviCivita_isCovariantDerivativeOn (g : SmoothRiemannianMetric I M)
    (α : M) :
    IsCovariantDerivativeOn (V := (TangentSpace I : M → Type _)) E
      (chartLeviCivita (I := I) g α) (chartLeviCivitaGoodSet (I := I) α) where
  add hσ hσ' hx := chartLeviCivita_add (I := I) g α hσ hσ' hx
  leibniz hσ hf hx := chartLeviCivita_leibniz (I := I) g α hσ hf hx

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Geometry.Connection.chartLeviCivita_isCovariantDerivativeOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Geometry.Connection.chartLeviCivita_isCovariantDerivativeOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Geometry.Connection.chartLeviCivita_isCovariantDerivativeOn ``Submission.DifferentialGeometry.Geometry.Connection.chartLeviCivita_isCovariantDerivativeOn

end Connection
end Geometry
end DifferentialGeometry
