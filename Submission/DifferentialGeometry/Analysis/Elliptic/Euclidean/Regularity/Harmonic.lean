import Submission.DifferentialGeometry.Analysis.Elliptic.Euclidean.Regularity.HigherOrder
import Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.Iterated

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.MeasureTheory _root_.Set
open scoped _root_.ENNReal _root_.InnerProductSpace _root_.ContDiff

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem matMulE_one (v : E) : DeGiorgi.matMulE 1 v = v := by
  ext i
  simp only [DeGiorgi.matMulE_apply, Matrix.one_mulVec]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.matMulE_one
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.matMulE_one target :: scope.openDecls } }

private def laplaceCoeff (Ω : Set E) : DeGiorgi.EllipticCoeff d Ω where
  a := fun _ => 1
  lam := 1
  Λ := 1
  measurable_comp := fun _ _ => measurable_const
  hlam := zero_lt_one
  hΛ := le_rfl
  coercive := Filter.Eventually.of_forall fun _ v => by
    rw [one_mul, matMulE_one, real_inner_self_eq_norm_sq]
  coercive_inv := Filter.Eventually.of_forall fun _ v => by
    rw [inv_one, one_mul, inv_one, matMulE_one, real_inner_self_eq_norm_sq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.laplaceCoeff
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.laplaceCoeff target :: scope.openDecls } }

private def laplaceForm :
    NirenbergEuclidean.SmoothEllipticBilinearForm d (Set.univ : Set E) where
  a := fun _ => 1
  c := fun _ => 0
  symm := by
    intro _ i j
    simp only [Matrix.one_apply, eq_comm]
  smooth_a := fun _ _ => contDiff_const
  smooth_c := contDiff_const
  lam := 1
  capLam := 1
  ellipticity_pos := zero_lt_one
  ellipticity_le_upper := le_rfl
  coercive := fun _ _ v => by
    rw [one_mul, matMulE_one, real_inner_self_eq_norm_sq]

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.laplaceForm
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.laplaceForm target :: scope.openDecls } }

private theorem isSolution_laplaceCoeff_of_integral_inner_weakGrad_smoothGrad_eq_zero
    {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hweak : ∀ (φ : E → ℝ), DeGiorgi.IsSmoothTestOn Ω φ →
      (∫ x in Ω, _root_.Inner.inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) :
    DeGiorgi.IsSolution (laplaceCoeff Ω) u := by
  apply DeGiorgi.isHomogeneousWeakSolution_isSolution
  refine ⟨hu.memW1p, ?_⟩
  apply DeGiorgi.bilinFormOfCoeff_eq_of_isSmoothTestOn hΩ (laplaceCoeff Ω)
    (fun _ => 0) (by intros; simp) (by intros; simp) 0 (by intros; simp) hu
  intro φ hφ
  simpa only [DeGiorgi.bilinFormOfCoeff, DeGiorgi.bilinFormIntegrandOfCoeff,
    laplaceCoeff, matMulE_one, DeGiorgi.smoothTestWitness] using hweak φ hφ

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.isSolution_laplaceCoeff_of_integral_inner_weakGrad_smoothGrad_eq_zero
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Sobolev.Euclidean.isSolution_laplaceCoeff_of_integral_inner_weakGrad_smoothGrad_eq_zero target :: scope.openDecls } }

theorem memWkp_of_integral_inner_weakGrad_smoothGrad_eq_zero
    (k : ℕ) {Ω V : Set E} (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hV_compact : IsCompact (closure V)) (hV_sub : closure V ⊆ Ω)
    {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hweak : ∀ (φ : E → ℝ), DeGiorgi.IsSmoothTestOn Ω φ →
      (∫ x in Ω, _root_.Inner.inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) :
    MemWkp (d := d) k 2 u V := by
  exact (isSolution_laplaceCoeff_of_integral_inner_weakGrad_smoothGrad_eq_zero
    hΩ hu hweak).memWkp k hΩ hV hV_compact hV_sub laplaceForm
      (rho := 1) one_ne_zero (by intros; simp only [laplaceCoeff, laplaceForm, one_mul])

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.memWkp_of_integral_inner_weakGrad_smoothGrad_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.memWkp_of_integral_inner_weakGrad_smoothGrad_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.memWkp_of_integral_inner_weakGrad_smoothGrad_eq_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.memWkp_of_integral_inner_weakGrad_smoothGrad_eq_zero

theorem exists_contDiffOn_ae_eq_of_integral_inner_weakGrad_smoothGrad_eq_zero
    {Ω V : Set E} (hΩ : IsOpen Ω) (hV : IsOpen V)
    (hV_compact : IsCompact (closure V)) (hV_sub : closure V ⊆ Ω)
    {u : E → ℝ} (hu : DeGiorgi.MemW1pWitness 2 u Ω)
    (hweak : ∀ (φ : E → ℝ), DeGiorgi.IsSmoothTestOn Ω φ →
      (∫ x in Ω, _root_.Inner.inner ℝ (hu.weakGrad x) (DeGiorgi.smoothGradField φ x)) = 0) :
    ∃ v : E → ℝ, ContDiffOn ℝ (∞ : WithTop ℕ∞) v V ∧
      u =ᵐ[volume.restrict V] v := by
  exact EuclideanIteratedEmbedding.exists_contDiffOn_ae_eq_of_forall_memWkp_two hV
    (fun k => memWkp_of_integral_inner_weakGrad_smoothGrad_eq_zero
      k hΩ hV hV_compact hV_sub hu hweak)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiffOn_ae_eq_of_integral_inner_weakGrad_smoothGrad_eq_zero then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiffOn_ae_eq_of_integral_inner_weakGrad_smoothGrad_eq_zero"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiffOn_ae_eq_of_integral_inner_weakGrad_smoothGrad_eq_zero ``Submission.DifferentialGeometry.Analysis.Sobolev.Euclidean.exists_contDiffOn_ae_eq_of_integral_inner_weakGrad_smoothGrad_eq_zero

end DifferentialGeometry.Analysis.Sobolev.Euclidean
