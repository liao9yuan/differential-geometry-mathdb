import Submission.DifferentialGeometry.Geometry.Boundary.Metric.Induced
import Submission.DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission


noncomputable section

open _root_.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.Matrix

namespace DifferentialGeometry
namespace Integral
namespace DivergenceTheorem
namespace WithBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

open _root_.Submission.DifferentialGeometry.Integral.Measure

def boundaryChartBasisVecFiber (α₀ : BoundaryManifold I M)
    (i : Fin (Module.finrank ℝ hI.boundaryE)) (α : BoundaryManifold I M) :
    TangentSpace hI.boundaryI α :=
  (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).symm α
    ((Module.finBasis ℝ hI.boundaryE) i)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVecFiber then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVecFiber"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVecFiber ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVecFiber

def boundaryChartBasisVec (α₀ : BoundaryManifold I M)
    (i : Fin (Module.finrank ℝ hI.boundaryE)) :
    BoundaryManifold I M →
      TotalSpace hI.boundaryE (TangentSpace hI.boundaryI : BoundaryManifold I M → Type _) :=
  fun α => TotalSpace.mk' hI.boundaryE α (boundaryChartBasisVecFiber α₀ i α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec

omit [FiniteDimensional ℝ E] in
@[simp] lemma boundaryChartBasisVec_proj
    (α₀ : BoundaryManifold I M) (i : Fin (Module.finrank ℝ hI.boundaryE))
    (α : BoundaryManifold I M) :
    (boundaryChartBasisVec (M := M) α₀ i α).proj = α := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec_proj then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec_proj"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec_proj ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec_proj

omit [FiniteDimensional ℝ E] in
@[simp] lemma boundaryChartBasisVec_snd
    (α₀ : BoundaryManifold I M) (i : Fin (Module.finrank ℝ hI.boundaryE))
    (α : BoundaryManifold I M) :
    (boundaryChartBasisVec (M := M) α₀ i α).2 =
      boundaryChartBasisVecFiber (M := M) α₀ i α := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec_snd ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec_snd

omit [FiniteDimensional ℝ E] in
lemma trivializationAt_boundaryChartBasisVec_snd
    (α₀ : BoundaryManifold I M) (i : Fin (Module.finrank ℝ hI.boundaryE))
    {α : BoundaryManifold I M}
    (hα : α ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet) :
    (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀
        ⟨α, boundaryChartBasisVecFiber (M := M) α₀ i α⟩).2
      = (Module.finBasis ℝ hI.boundaryE) i := by
  have h := (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).apply_mk_symm hα
    ((Module.finBasis ℝ hI.boundaryE) i)
  simpa [boundaryChartBasisVecFiber] using congrArg Prod.snd h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.trivializationAt_boundaryChartBasisVec_snd then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.trivializationAt_boundaryChartBasisVec_snd"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.trivializationAt_boundaryChartBasisVec_snd ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.trivializationAt_boundaryChartBasisVec_snd

omit [FiniteDimensional ℝ E] in
lemma boundaryChartBasisVec_contMDiffOn
    (α₀ : BoundaryManifold I M) (i : Fin (Module.finrank ℝ hI.boundaryE)) :
    ContMDiffOn hI.boundaryI (hI.boundaryI.prod 𝓘(ℝ, hI.boundaryE)) ∞
      (boundaryChartBasisVec (M := M) α₀ i)
      (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet := by
  have hiff :=
    ((_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀)).contMDiffOn_section_baseSet_iff
      (IB := hI.boundaryI) (n := ∞)
      (s := fun α => boundaryChartBasisVecFiber (M := M) α₀ i α)
  refine hiff.mpr ?_
  have hconst : ContMDiffOn hI.boundaryI 𝓘(ℝ, hI.boundaryE) ∞
      (fun _ : BoundaryManifold I M => (Module.finBasis ℝ hI.boundaryE) i)
      (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet :=
    contMDiffOn_const
  refine hconst.congr ?_
  intro α hα
  exact (trivializationAt_boundaryChartBasisVec_snd (M := M) α₀ i hα)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec_contMDiffOn ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisVec_contMDiffOn

def boundaryChartBasisFamily (α₀ : BoundaryManifold I M) {α : BoundaryManifold I M}
    (hα : α ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet) :
    Module.Basis (Fin (Module.finrank ℝ hI.boundaryE)) ℝ (TangentSpace hI.boundaryI α) :=
  (Module.finBasis ℝ hI.boundaryE).map
    (ContinuousLinearEquiv.toLinearEquiv
      ((_root_.FiberBundle.trivializationAt hI.boundaryE
        (TangentSpace hI.boundaryI) α₀).continuousLinearEquivAt ℝ α hα).symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisFamily then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisFamily"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisFamily ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisFamily

omit [FiniteDimensional ℝ E] in
lemma boundaryChartBasisFamily_apply
    (α₀ : BoundaryManifold I M) {α : BoundaryManifold I M}
    (hα : α ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet)
    (i : Fin (Module.finrank ℝ hI.boundaryE)) :
    boundaryChartBasisFamily (M := M) α₀ hα i =
      boundaryChartBasisVecFiber (M := M) α₀ i α := by
  unfold boundaryChartBasisFamily boundaryChartBasisVecFiber
  rw [Module.Basis.map_apply]
  rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisFamily_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisFamily_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisFamily_apply ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisFamily_apply

omit [FiniteDimensional ℝ E] in
lemma boundaryChartBasisFamily_linearIndependent
    (α₀ : BoundaryManifold I M) {α : BoundaryManifold I M}
    (hα : α ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet) :
    LinearIndependent ℝ
      (fun i : Fin (Module.finrank ℝ hI.boundaryE) =>
        boundaryChartBasisVecFiber (M := M) α₀ i α) := by
  have h := (boundaryChartBasisFamily (M := M) α₀ hα).linearIndependent
  have hcongr :
      (boundaryChartBasisFamily (M := M) α₀ hα :
        Fin (Module.finrank ℝ hI.boundaryE) → TangentSpace hI.boundaryI α)
      = fun i => boundaryChartBasisVecFiber (M := M) α₀ i α := by
    funext i
    exact boundaryChartBasisFamily_apply (M := M) α₀ hα i
  rw [← hcongr]
  exact h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisFamily_linearIndependent then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisFamily_linearIndependent"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisFamily_linearIndependent ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryChartBasisFamily_linearIndependent

def boundaryGramMatrix (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) (α : BoundaryManifold I M) :
    Matrix (Fin (Module.finrank ℝ hI.boundaryE))
      (Fin (Module.finrank ℝ hI.boundaryE)) ℝ :=
  Matrix.of fun i j =>
    inducedMetricInner (M := M) g α
      (boundaryChartBasisVecFiber (M := M) α₀ i α)
      (boundaryChartBasisVecFiber (M := M) α₀ j α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix

omit [FiniteDimensional ℝ E] in
@[simp] lemma boundaryGramMatrix_apply
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) (α : BoundaryManifold I M)
    (i j : Fin (Module.finrank ℝ hI.boundaryE)) :
    boundaryGramMatrix (M := M) g α₀ α i j =
      inducedMetricInner (M := M) g α
        (boundaryChartBasisVecFiber (M := M) α₀ i α)
        (boundaryChartBasisVecFiber (M := M) α₀ j α) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_apply then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_apply"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_apply ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_apply

omit [FiniteDimensional ℝ E] in
lemma boundaryGramMatrix_isHermitian
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) (α : BoundaryManifold I M) :
    (boundaryGramMatrix (M := M) g α₀ α).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  show _root_.Star.star (boundaryGramMatrix (M := M) g α₀ α j i) =
    boundaryGramMatrix (M := M) g α₀ α i j
  rw [boundaryGramMatrix_apply, boundaryGramMatrix_apply, _root_.TrivialStar.star_trivial]
  exact inducedMetricInner_symm (M := M) g α
    (boundaryChartBasisVecFiber (M := M) α₀ j α)
    (boundaryChartBasisVecFiber (M := M) α₀ i α)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_isHermitian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_isHermitian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_isHermitian ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_isHermitian

omit [FiniteDimensional ℝ E] in
lemma boundaryGramMatrix_dotProduct_mulVec
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) (α : BoundaryManifold I M)
    (c : Fin (Module.finrank ℝ hI.boundaryE) → ℝ) :
    star c ⬝ᵥ (boundaryGramMatrix (M := M) g α₀ α) *ᵥ c =
      inducedMetricInner (M := M) g α
        (∑ i, c i • boundaryChartBasisVecFiber (M := M) α₀ i α)
        (∑ j, c j • boundaryChartBasisVecFiber (M := M) α₀ j α) := by
  have hexpand' :
      inducedMetricInner (M := M) g α
          (∑ i, c i • boundaryChartBasisVecFiber (M := M) α₀ i α)
          (∑ j, c j • boundaryChartBasisVecFiber (M := M) α₀ j α)
        = ∑ i, ∑ j, (c i * c j) *
            inducedMetricInner (M := M) g α
              (boundaryChartBasisVecFiber (M := M) α₀ i α)
              (boundaryChartBasisVecFiber (M := M) α₀ j α) := by
    have hL :
        inducedMetricInner (M := M) g α
            (∑ i, c i • boundaryChartBasisVecFiber (M := M) α₀ i α)
          = ∑ i, c i • inducedMetricInner (M := M) g α
              (boundaryChartBasisVecFiber (M := M) α₀ i α) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      exact ContinuousLinearMap.map_smul _ _ _
    rw [hL]
    rw [sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [smul_apply]
    have hR :
        (inducedMetricInner (M := M) g α
            (boundaryChartBasisVecFiber (M := M) α₀ i α))
            (∑ j, c j • boundaryChartBasisVecFiber (M := M) α₀ j α)
          = ∑ j, c j *
              (inducedMetricInner (M := M) g α
                (boundaryChartBasisVecFiber (M := M) α₀ i α))
                (boundaryChartBasisVecFiber (M := M) α₀ j α) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [← smul_eq_mul]
      exact ContinuousLinearMap.map_smul _ _ _
    rw [hR, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hexpand']
  simp only [dotProduct, Matrix.mulVec, boundaryGramMatrix_apply, Pi.star_apply, _root_.TrivialStar.star_trivial]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_dotProduct_mulVec then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_dotProduct_mulVec"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_dotProduct_mulVec ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_dotProduct_mulVec

omit [FiniteDimensional ℝ E] in
lemma boundaryGramMatrix_posDef
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) {α : BoundaryManifold I M}
    (hα : α ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet) :
    (boundaryGramMatrix (M := M) g α₀ α).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (boundaryGramMatrix_isHermitian (M := M) g α₀ α) ?_
  intro c hc
  set w : TangentSpace hI.boundaryI α :=
    ∑ i, c i • boundaryChartBasisVecFiber (M := M) α₀ i α with hw_def
  have heq := boundaryGramMatrix_dotProduct_mulVec (M := M) g α₀ α c
  rw [heq]
  have hwnz : w ≠ 0 := by
    intro hw0
    have hli := boundaryChartBasisFamily_linearIndependent (M := M) α₀ hα
    rw [Fintype.linearIndependent_iff] at hli
    have : c = 0 := funext (hli c hw0)
    exact hc this
  exact inducedMetricInner_pos (M := M) g α w hwnz

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_posDef then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_posDef"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_posDef ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_posDef

omit [FiniteDimensional ℝ E] in
lemma boundaryGramMatrix_det_pos
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) {α : BoundaryManifold I M}
    (hα : α ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet) :
    0 < (boundaryGramMatrix (M := M) g α₀ α).det :=
  (boundaryGramMatrix_posDef (M := M) g α₀ hα).det_pos

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_det_pos then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_det_pos"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_det_pos ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_det_pos

omit [FiniteDimensional ℝ E] in
theorem boundaryGramMatrix_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M)
    (i j : Fin (Module.finrank ℝ hI.boundaryE)) :
    ContMDiffOn hI.boundaryI 𝓘(ℝ) ∞
      (fun α => boundaryGramMatrix (M := M) g α₀ α i j)
      (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet := by
  have hg : ContMDiffOn hI.boundaryI
      (hI.boundaryI.prod 𝓘(ℝ, hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)) ∞
      (fun b : BoundaryManifold I M => TotalSpace.mk' (hI.boundaryE →L[ℝ] hI.boundaryE →L[ℝ] ℝ)
        (E := fun y => TangentSpace hI.boundaryI y →L[ℝ] TangentSpace hI.boundaryI y →L[ℝ] ℝ)
        b (inducedMetricInner (M := M) g b))
      (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet :=
    (inducedMetricInner_contMDiff (M := M) g).contMDiffOn
  have hv := boundaryChartBasisVec_contMDiffOn (M := M) α₀ i
  have hw := boundaryChartBasisVec_contMDiffOn (M := M) α₀ j
  have happ :
      ContMDiffOn hI.boundaryI (hI.boundaryI.prod 𝓘(ℝ, ℝ)) ∞
        (fun α : BoundaryManifold I M => (⟨α,
            inducedMetricInner (M := M) g α
              (boundaryChartBasisVecFiber (M := M) α₀ i α)
              (boundaryChartBasisVecFiber (M := M) α₀ j α)⟩ :
              _root_.Bundle.TotalSpace ℝ (Bundle.Trivial (BoundaryManifold I M) ℝ)))
        (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet :=
    ContMDiffOn.clm_bundle_apply₂
      (F₁ := hI.boundaryE) (F₂ := hI.boundaryE) (F₃ := ℝ)
      (b := id) hg hv hw
  intro α hα
  have hpα := happ α hα
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpα
  exact hpα.2

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_entry_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_entry_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_entry_contMDiffOn ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_entry_contMDiffOn

omit [FiniteDimensional ℝ E] in
lemma boundaryGramMatrix_det_contMDiffOn
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) :
    ContMDiffOn hI.boundaryI 𝓘(ℝ) ∞
      (fun α => (boundaryGramMatrix (M := M) g α₀ α).det)
      (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet := by
  classical
  have hexp :
      (fun α : BoundaryManifold I M => (boundaryGramMatrix (M := M) g α₀ α).det)
        = (fun α : BoundaryManifold I M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ hI.boundaryE)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ i, boundaryGramMatrix (M := M) g α₀ α (σ i) i) := by
    funext α
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finsetSum (fun σ _ => ?_)
  refine ContMDiffOn.mul
    (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finsetProd (fun i _ => ?_)
  exact boundaryGramMatrix_entry_contMDiffOn (M := M) g α₀ (σ i) i

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_det_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_det_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_det_contMDiffOn ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_det_contMDiffOn

def boundaryInvGramMatrix (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) (α : BoundaryManifold I M) :
    Matrix (Fin (Module.finrank ℝ hI.boundaryE))
      (Fin (Module.finrank ℝ hI.boundaryE)) ℝ :=
  (boundaryGramMatrix (M := M) g α₀ α)⁻¹

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInvGramMatrix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInvGramMatrix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInvGramMatrix ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInvGramMatrix

omit [FiniteDimensional ℝ E] in
lemma boundaryInvGramMatrix_mul_boundaryGramMatrix
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) {α : BoundaryManifold I M}
    (hα : α ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet) :
    boundaryInvGramMatrix (M := M) g α₀ α *
      boundaryGramMatrix (M := M) g α₀ α = 1 := by
  have hpos := boundaryGramMatrix_posDef (M := M) g α₀ hα
  have hdet_unit : IsUnit (boundaryGramMatrix (M := M) g α₀ α).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold boundaryInvGramMatrix
  exact Matrix.nonsing_inv_mul _ hdet_unit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInvGramMatrix_mul_boundaryGramMatrix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInvGramMatrix_mul_boundaryGramMatrix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInvGramMatrix_mul_boundaryGramMatrix ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInvGramMatrix_mul_boundaryGramMatrix

omit [FiniteDimensional ℝ E] in
lemma boundaryGramMatrix_mul_boundaryInvGramMatrix
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M) {α : BoundaryManifold I M}
    (hα : α ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet) :
    boundaryGramMatrix (M := M) g α₀ α *
      boundaryInvGramMatrix (M := M) g α₀ α = 1 := by
  have hpos := boundaryGramMatrix_posDef (M := M) g α₀ hα
  have hdet_unit : IsUnit (boundaryGramMatrix (M := M) g α₀ α).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold boundaryInvGramMatrix
  exact Matrix.mul_nonsing_inv _ hdet_unit

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_mul_boundaryInvGramMatrix then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_mul_boundaryInvGramMatrix"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_mul_boundaryInvGramMatrix ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_mul_boundaryInvGramMatrix

omit [FiniteDimensional ℝ E] in
lemma boundaryGramMatrix_adjugate_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M)
    (i j : Fin (Module.finrank ℝ hI.boundaryE)) :
    ContMDiffOn hI.boundaryI 𝓘(ℝ) ∞
      (fun α : BoundaryManifold I M =>
        (boundaryGramMatrix (M := M) g α₀ α).adjugate i j)
      (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet := by
  classical
  have hexp : (fun α : BoundaryManifold I M =>
        (boundaryGramMatrix (M := M) g α₀ α).adjugate i j) =
      (fun α : BoundaryManifold I M =>
        ((boundaryGramMatrix (M := M) g α₀ α).updateRow j
          (Pi.single i (1 : ℝ))).det) := by
    funext α
    exact Matrix.adjugate_apply _ _ _
  rw [hexp]
  have hexp2 : (fun α : BoundaryManifold I M =>
        ((boundaryGramMatrix (M := M) g α₀ α).updateRow j
          (Pi.single i (1 : ℝ))).det) =
      (fun α : BoundaryManifold I M =>
        ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ hI.boundaryE)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ k, (boundaryGramMatrix (M := M) g α₀ α).updateRow j
                (Pi.single i (1 : ℝ)) (σ k) k) := by
    funext α
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finsetSum (fun σ _ => ?_)
  refine ContMDiffOn.mul (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finsetProd (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq : (fun α : BoundaryManifold I M =>
        (boundaryGramMatrix (M := M) g α₀ α).updateRow j
          (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun _ : BoundaryManifold I M =>
          (Pi.single (M := fun _ : Fin (Module.finrank ℝ hI.boundaryE) => ℝ) i
            (1 : ℝ)) k) := by
      funext α
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq : (fun α : BoundaryManifold I M =>
        (boundaryGramMatrix (M := M) g α₀ α).updateRow j
          (Pi.single i (1 : ℝ)) (σ k) k) =
        (fun α : BoundaryManifold I M =>
          boundaryGramMatrix (M := M) g α₀ α (σ k) k) := by
      funext α
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    exact boundaryGramMatrix_entry_contMDiffOn (M := M) g α₀ (σ k) k

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_adjugate_entry_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_adjugate_entry_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_adjugate_entry_contMDiffOn ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryGramMatrix_adjugate_entry_contMDiffOn

omit [FiniteDimensional ℝ E] in
theorem boundaryInvGramMatrix_entry_contMDiffOn
    (g : SmoothRiemannianMetric I M)
    (α₀ : BoundaryManifold I M)
    (i j : Fin (Module.finrank ℝ hI.boundaryE)) :
    ContMDiffOn hI.boundaryI 𝓘(ℝ) ∞
      (fun α : BoundaryManifold I M =>
        boundaryInvGramMatrix (M := M) g α₀ α i j)
      (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet := by
  classical
  have hcongr : ∀ α ∈ (_root_.FiberBundle.trivializationAt hI.boundaryE
      (TangentSpace hI.boundaryI) α₀).baseSet,
      boundaryInvGramMatrix (M := M) g α₀ α i j =
        ((boundaryGramMatrix (M := M) g α₀ α).det)⁻¹ *
          (boundaryGramMatrix (M := M) g α₀ α).adjugate i j := by
    intro α hα
    have hdet_pos := boundaryGramMatrix_det_pos (M := M) g α₀ hα
    have hdet_ne : (boundaryGramMatrix (M := M) g α₀ α).det ≠ 0 := ne_of_gt hdet_pos
    unfold boundaryInvGramMatrix
    rw [Matrix.inv_def]
    change (Ring.inverse (boundaryGramMatrix (M := M) g α₀ α).det •
            (boundaryGramMatrix (M := M) g α₀ α).adjugate) i j =
      ((boundaryGramMatrix (M := M) g α₀ α).det)⁻¹ *
          (boundaryGramMatrix (M := M) g α₀ α).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContMDiffOn.congr ?_ hcongr
  refine ContMDiffOn.mul ?_ ?_
  · have hdet_smooth : ContMDiffOn hI.boundaryI 𝓘(ℝ) ∞
        (fun α : BoundaryManifold I M =>
          (boundaryGramMatrix (M := M) g α₀ α).det)
        (_root_.FiberBundle.trivializationAt hI.boundaryE (TangentSpace hI.boundaryI) α₀).baseSet :=
      boundaryGramMatrix_det_contMDiffOn (M := M) g α₀
    intro α hα
    have hdet_pos := boundaryGramMatrix_det_pos (M := M) g α₀ hα
    have hdet_ne : (boundaryGramMatrix (M := M) g α₀ α).det ≠ 0 := ne_of_gt hdet_pos
    have hsmooth_inv : ContDiffAt ℝ ∞ (fun y : ℝ => y⁻¹)
        (boundaryGramMatrix (M := M) g α₀ α).det := contDiffAt_inv _ hdet_ne
    have h_at := hdet_smooth α hα
    exact hsmooth_inv.contMDiffAt.comp_contMDiffWithinAt α h_at
  · exact boundaryGramMatrix_adjugate_entry_contMDiffOn (M := M) g α₀ i j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInvGramMatrix_entry_contMDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInvGramMatrix_entry_contMDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInvGramMatrix_entry_contMDiffOn ``Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.boundaryInvGramMatrix_entry_contMDiffOn

end WithBoundary
end DivergenceTheorem
end Integral
end DifferentialGeometry
