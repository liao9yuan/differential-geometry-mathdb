import Submission.DifferentialGeometry.Analysis.Calculus.Variation.Quadratic
import Submission.DifferentialGeometry.External.DeGiorgi.SobolevSpace.Witnesses
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Composition
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Set
open scoped _root_.ENNReal _root_.ContDiff

namespace DeGiorgi

variable {d n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)
local notation "F" => EuclideanSpace ℝ (Fin n)

def MemW1pWitness.ofContDiffComponentHasCompactSupport
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsOpen Ω)
    {φ : E → F} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ) (i : Fin n) :
    MemW1pWitness p (fun x => φ x i) Ω :=
  MemW1pWitness.restrict hΩ (_root_.Set.subset_univ Ω)
    (MemW1pWitness.ofContDiffHasCompactSupport
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hφ)
      (hφs.comp_left (g := EuclideanSpace.proj (𝕜 := ℝ) i) (map_zero _)))

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.MemW1pWitness.ofContDiffComponentHasCompactSupport then
    throwError "Refusing to shadow existing declaration DeGiorgi.MemW1pWitness.ofContDiffComponentHasCompactSupport"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.MemW1pWitness.ofContDiffComponentHasCompactSupport ``Submission.DeGiorgi.MemW1pWitness.ofContDiffComponentHasCompactSupport

theorem MemW1pWitness.ofContDiffComponentHasCompactSupport_weakGrad
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsOpen Ω)
    {φ : E → F} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (i : Fin n) (x : E) (j : Fin d) :
    (MemW1pWitness.ofContDiffComponentHasCompactSupport (p := p) hΩ hφ hφs i).weakGrad x j =
      (fderiv ℝ φ x (EuclideanSpace.single j 1)) i := by
  change fderiv ℝ (fun y => φ y i) x (EuclideanSpace.single j 1) = _
  have hcomp := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt).comp x
    ((hφ.differentiable (by simp)) x).hasFDerivAt
  simpa only [EuclideanSpace.coe_proj, Function.comp_def, ContinuousLinearMap.comp_apply] using
    congrArg (fun L : E →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) hcomp.fderiv

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.MemW1pWitness.ofContDiffComponentHasCompactSupport_weakGrad then
    throwError "Refusing to shadow existing declaration DeGiorgi.MemW1pWitness.ofContDiffComponentHasCompactSupport_weakGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.MemW1pWitness.ofContDiffComponentHasCompactSupport_weakGrad ``Submission.DeGiorgi.MemW1pWitness.ofContDiffComponentHasCompactSupport_weakGrad

theorem memW01p_of_contDiffComponentHasCompactSupport_subset
    {p : ℝ≥0∞} {Ω : Set E} (hΩ : IsOpen Ω)
    {φ : E → F} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ Ω) (i : Fin n) :
    MemW01p p (fun x => φ x i) Ω := by
  let hw := MemW1pWitness.ofContDiffComponentHasCompactSupport (p := p) hΩ hφ hφs i
  refine ⟨hw.memW1p, hw, fun _ => fun x => φ x i, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hφ
  · intro k
    exact hφs.comp_left (g := EuclideanSpace.proj (𝕜 := ℝ) i) (map_zero _)
  · intro k
    simpa only [EuclideanSpace.coe_proj, Function.comp_def] using
      (tsupport_comp_subset (g := EuclideanSpace.proj (𝕜 := ℝ) i) (map_zero _) φ).trans hφ_sub
  · simp
  · intro j
    simp [hw, MemW1pWitness.ofContDiffComponentHasCompactSupport,
      MemW1pWitness.restrict, MemW1pWitness.ofContDiffHasCompactSupport]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.memW01p_of_contDiffComponentHasCompactSupport_subset then
    throwError "Refusing to shadow existing declaration DeGiorgi.memW01p_of_contDiffComponentHasCompactSupport_subset"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.memW01p_of_contDiffComponentHasCompactSupport_subset ``Submission.DeGiorgi.memW01p_of_contDiffComponentHasCompactSupport_subset

def componentAffineVariationWitness
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → F}
    (hu : ∀ i : Fin n, MemW1pWitness 2 (fun x => u x i) Ω)
    {φ : E → F} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ) (t : ℝ)
    (i : Fin n) : MemW1pWitness 2 (fun x => (u x + t • φ x) i) Ω :=
  by
    simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using
      (hu i).add ((MemW1pWitness.ofContDiffComponentHasCompactSupport hΩ hφ hφs i).smul t)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.componentAffineVariationWitness then
    throwError "Refusing to shadow existing declaration DeGiorgi.componentAffineVariationWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.componentAffineVariationWitness ``Submission.DeGiorgi.componentAffineVariationWitness

theorem componentAffineVariationWitness_weakGrad
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → F}
    (hu : ∀ i : Fin n, MemW1pWitness 2 (fun x => u x i) Ω)
    {φ : E → F} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (t : ℝ) (i : Fin n) (x : E) (j : Fin d) :
    (componentAffineVariationWitness hΩ hu hφ hφs t i).weakGrad x j =
      (hu i).weakGrad x j + t * (fderiv ℝ φ x (EuclideanSpace.single j 1)) i := by
  change (hu i).weakGrad x j + t *
    (MemW1pWitness.ofContDiffComponentHasCompactSupport (p := 2) hΩ hφ hφs i).weakGrad x j = _
  rw [MemW1pWitness.ofContDiffComponentHasCompactSupport_weakGrad]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.componentAffineVariationWitness_weakGrad then
    throwError "Refusing to shadow existing declaration DeGiorgi.componentAffineVariationWitness_weakGrad"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.componentAffineVariationWitness_weakGrad ``Submission.DeGiorgi.componentAffineVariationWitness_weakGrad

def weakGradientColumn
    {p : ℝ≥0∞} {Ω : Set E} {u : E → F}
    (hu : ∀ i : Fin n, MemW1pWitness p (fun x => u x i) Ω) (x : E) (j : Fin d) : F :=
  WithLp.toLp 2 fun i => (hu i).weakGrad x j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.weakGradientColumn then
    throwError "Refusing to shadow existing declaration DeGiorgi.weakGradientColumn"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.weakGradientColumn ``Submission.DeGiorgi.weakGradientColumn

theorem weakGradientColumn_componentAffineVariationWitness
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → F}
    (hu : ∀ i : Fin n, MemW1pWitness 2 (fun x => u x i) Ω)
    {φ : E → F} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ)
    (t : ℝ) (x : E) (j : Fin d) :
    weakGradientColumn (componentAffineVariationWitness hΩ hu hφ hφs t) x j =
      weakGradientColumn hu x j + t • fderiv ℝ φ x (EuclideanSpace.single j 1) := by
  ext i
  simpa only [weakGradientColumn, PiLp.toLp_apply, PiLp.add_apply, PiLp.smul_apply,
    smul_eq_mul] using componentAffineVariationWitness_weakGrad hΩ hu hφ hφs t i x j

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.weakGradientColumn_componentAffineVariationWitness then
    throwError "Refusing to shadow existing declaration DeGiorgi.weakGradientColumn_componentAffineVariationWitness"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.weakGradientColumn_componentAffineVariationWitness ``Submission.DeGiorgi.weakGradientColumn_componentAffineVariationWitness


end DeGiorgi

end

noncomputable section

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Submission.MeasureTheory
open _root_.Submission.DifferentialGeometry.Analysis.Sobolev
open scoped _root_.Topology _root_.ContDiff _root_.ENNReal

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d m n : ℕ}

local notation "P" => EuclideanSpace ℝ (Fin d)
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin n)

theorem exists_coordinate_affine_variation_memW1p
    {Ω : Set P} (hΩ : IsOpen Ω) {z : P → E}
    (hz : ∀ i, DeGiorgi.MemW1pWitness 2 (fun x => z x i) Ω)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hzK : ∀ᵐ x ∂volume.restrict Ω, z x ∈ K)
    (β : E → F) (hβ : ContDiffOn ℝ ∞ β U)
    {x₀ : P} {a : ℝ} (hball : Metric.closedBall x₀ a ⊆ Ω)
    {φ : P → E} (hφ : ContDiff ℝ ∞ φ) (hφs : HasCompactSupport φ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t| < δ →
      ∃ hqt : ∀ i, DeGiorgi.MemW1pWitness 2
        (fun x => β (z x + t • φ x) i) (Metric.ball x₀ a),
        (∀ᵐ x ∂volume.restrict (Metric.ball x₀ a), z x + t • φ x ∈ U) ∧
        (∀ᵐ x ∂volume.restrict (Metric.ball x₀ a), ∀ j,
          DeGiorgi.weakGradientColumn hqt x j =
            fderiv ℝ β (z x + t • φ x)
              (DeGiorgi.weakGradientColumn hz x j +
                t • fderiv ℝ φ x (EuclideanSpace.single j 1))) ∧
        (∀ x, x ∉ tsupport φ → β (z x + t • φ x) = β (z x)) := by
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  let L := Metric.cthickening ε K
  have hL : IsCompact L := hK.cthickening
  obtain ⟨T, hT, hTc, hTeq⟩ :=
    DifferentialGeometry.Analysis.exists_contDiff_compactSupport_extension_on_isCompact hL hU hεU hβ
  obtain ⟨C, hC⟩ := (hT.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hTc.fderiv (𝕜 := ℝ))
  obtain ⟨B, hB⟩ := hφ.continuous.bounded_above_of_compact_support hφs
  let D := _root_.Max.max B 0 + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨ε / D, div_pos hε hD, ?_⟩
  intro t ht
  have hmem : ∀ᵐ x ∂volume.restrict Ω, z x + t • φ x ∈ L := by
    filter_upwards [hzK] with x hx
    apply Metric.mem_cthickening_of_dist_le _ (z x) ε K hx
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have hφB : ‖φ x‖ ≤ D := (hB x).trans ((le_max_left B 0).trans (by dsimp [D]; linarith))
    have hmul := mul_lt_mul_of_pos_right ht hD
    rw [div_mul_cancel₀ _ hD.ne'] at hmul
    exact ((mul_le_mul_of_nonneg_left hφB (abs_nonneg t)).trans hmul.le)
  let haff := DeGiorgi.componentAffineVariationWitness hΩ hz hφ hφs t
  obtain ⟨hqT, hqTgrad⟩ := exists_memW1pWitnesses_comp_contDiff_on_ball hΩ haff T
    (hT.of_le (by simp)) hC hball
  have hmemB : ∀ᵐ x ∂volume.restrict (Metric.ball x₀ a), z x + t • φ x ∈ L :=
    _root_.MeasureTheory.ae_mono (Measure.restrict_mono_set _root_.MeasureTheory.MeasureSpace.volume
      (Metric.ball_subset_closedBall.trans hball)) hmem
  have heq (x : P) (hx : z x + t • φ x ∈ L) : T =ᶠ[𝓝 (z x + t • φ x)] β :=
    hTeq.filter_mono (nhds_le_nhdsSet hx)
  let hqt (i : Fin n) : DeGiorgi.MemW1pWitness 2
      (fun x => β (z x + t • φ x) i) (Metric.ball x₀ a) :=
    (hqT i).congr (hmemB.mono fun x hx =>
      congrArg (fun y : F => y i) (heq x hx).eq_of_nhds)
  refine ⟨hqt, hmemB.mono fun x hx => hεU hx, ?_, ?_⟩
  · filter_upwards [hmemB] with x hx
    intro j
    have hcol : DeGiorgi.weakGradientColumn hqt x j =
        fderiv ℝ T (z x + t • φ x) (DeGiorgi.weakGradientColumn haff x j) := by
      ext i
      exact hqTgrad i x j
    rw [hcol, (heq x hx).fderiv_eq, DeGiorgi.weakGradientColumn_componentAffineVariationWitness]
  · intro x hx
    rw [DeGiorgi.affineVariation_eq_of_notMem_tsupport t hx]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_coordinate_affine_variation_memW1p then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_coordinate_affine_variation_memW1p"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_coordinate_affine_variation_memW1p ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_coordinate_affine_variation_memW1p

end DifferentialGeometry.Analysis.Sobolev.Euclidean

end

section

open _root_.MeasureTheory _root_.Submission.MeasureTheory
open scoped _root_.BigOperators _root_.ENNReal

namespace DeGiorgi

theorem weakGrad_column_memLp
    {d : ℕ} {ι : Type*} [Fintype ι]
    {p : ℝ≥0∞} {Ω : Set (EuclideanSpace ℝ (Fin d))}
    {μ : _root_.MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))}
    {u : ι → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : ∀ i, MemW1pWitness p (u i) Ω μ) (j : Fin d) :
    _root_.MeasureTheory.MemLp (fun x => (WithLp.toLp 2 (fun i => (hu i).weakGrad x j) :
      EuclideanSpace ℝ ι)) p (μ.restrict Ω) := by
  exact MemLp.of_eval_piLp (fun i => (hu i).weakGrad_component_memLp j)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DeGiorgi.weakGrad_column_memLp then
    throwError "Refusing to shadow existing declaration DeGiorgi.weakGrad_column_memLp"
  Lean.modifyEnv fun env => Lean.addAlias env `DeGiorgi.weakGrad_column_memLp ``Submission.DeGiorgi.weakGrad_column_memLp

end DeGiorgi

end
