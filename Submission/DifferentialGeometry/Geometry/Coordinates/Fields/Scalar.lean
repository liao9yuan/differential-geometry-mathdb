import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff

namespace DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def scalarOnE (x₀ : M) (f : M → ℝ) : E → ℝ :=
  fun y => f ((extChartAt I x₀).symm y)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.scalarOnE then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.scalarOnE"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.scalarOnE ``Submission.DifferentialGeometry.Tensor.Coordinates.scalarOnE

omit [IsManifold I ∞ M] in
@[simp] lemma scalarOnE_def (x₀ : M) (f : M → ℝ) (y : E) :
    scalarOnE (I := I) x₀ f y = f ((extChartAt I x₀).symm y) := rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.scalarOnE_def then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.scalarOnE_def"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.scalarOnE_def ``Submission.DifferentialGeometry.Tensor.Coordinates.scalarOnE_def

omit [IsManifold I ∞ M] in
lemma scalarOnE_extChartAt (x₀ : M) (f : M → ℝ) {x : M}
    (hx : x ∈ (extChartAt I x₀).source) :
    scalarOnE (I := I) x₀ f (extChartAt I x₀ x) = f x := by
  change f ((extChartAt I x₀).symm (extChartAt I x₀ x)) = f x
  rw [(extChartAt I x₀).left_inv hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.scalarOnE_extChartAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.scalarOnE_extChartAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.scalarOnE_extChartAt ``Submission.DifferentialGeometry.Tensor.Coordinates.scalarOnE_extChartAt

lemma scalarOnE_contDiffOn (x₀ : M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContDiffOn ℝ ∞ (scalarOnE (I := I) x₀ f)
      (extChartAt I x₀).target := by
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I x₀).symm
      (extChartAt I x₀).target := contMDiffOn_extChartAt_symm (I := I) x₀
  have hf_on : ContMDiffOn I 𝓘(ℝ) ∞ f univ := hf.contMDiffOn
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (f ∘ (extChartAt I x₀).symm) (extChartAt I x₀).target :=
    hf_on.comp hsymm (fun _ _ => _root_.Set.mem_univ _)
  exact hcomp.contDiffOn

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffOn then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffOn"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffOn ``Submission.DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffOn

lemma scalarOnE_contDiffOn_prod
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (x₀ : M) {f : P → M → ℝ} {s : Set P}
    (hf : ContMDiffOn (𝓘(ℝ, P).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : P × M => f p.1 p.2) (s ×ˢ _root_.Set.univ)) :
    ContDiffOn ℝ ∞
      (fun p : P × E => scalarOnE (I := I) x₀ (f p.1) p.2)
      (s ×ˢ (extChartAt I x₀).target) := by
  have hfst : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) 𝓘(ℝ, P) ∞
      (fun p : P × E => p.1) (s ×ˢ (extChartAt I x₀).target) :=
    contMDiffOn_fst
  have hsnd : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) I ∞
      (fun p : P × E => (extChartAt I x₀).symm p.2)
      (s ×ˢ (extChartAt I x₀).target) := by
    refine (contMDiffOn_extChartAt_symm (I := I) x₀).comp contMDiffOn_snd ?_
    exact fun _ hp => hp.2
  have hpair : ContMDiffOn (𝓘(ℝ, P).prod 𝓘(ℝ, E)) (𝓘(ℝ, P).prod I) ∞
      (fun p : P × E => (p.1, (extChartAt I x₀).symm p.2))
      (s ×ˢ (extChartAt I x₀).target) :=
    hfst.prodMk hsnd
  have hcomp := hf.comp hpair (fun _ hp => ⟨hp.1, _root_.Set.mem_univ _⟩)
  have hcont : ContDiffOn ℝ ∞
      (fun p : P × E => f p.1 ((extChartAt I x₀).symm p.2))
      (s ×ˢ (extChartAt I x₀).target) := by
    rw [← contMDiffOn_iff_contDiffOn, modelWithCornersSelf_prod,
      ← chartedSpaceSelf_prod]
    exact hcomp
  simpa only [scalarOnE_def] using hcont

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffOn_prod then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffOn_prod"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffOn_prod ``Submission.DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffOn_prod

lemma scalarOnE_contDiffWithinAt
    (x₀ : M) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    ContDiffWithinAt ℝ ∞ (scalarOnE (I := I) x₀ f)
      (extChartAt I x₀).target y :=
  scalarOnE_contDiffOn (I := I) x₀ hf y hy

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffWithinAt then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffWithinAt"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffWithinAt ``Submission.DifferentialGeometry.Tensor.Coordinates.scalarOnE_contDiffWithinAt

end DifferentialGeometry.Tensor.Coordinates
