import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Submission.DifferentialGeometry.Analysis.FiniteDimensional.Coercivity
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.LinearAlgebra.Matrix.BilinearForm

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section

open _root_.Matrix _root_.Set
open scoped _root_.RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Schauder

private abbrev Euc (n : Type*) := EuclideanSpace Real n

run_cmd do
  let target := ``Submission.DifferentialGeometry.Analysis.Schauder.Euc
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Analysis.Schauder.Euc target :: scope.openDecls } }

theorem exists_uniform_matrix_quadratic_lower_bound
    {X n : Type*} [TopologicalSpace X]
    [Fintype n]
    {K : Set X} (hK : IsCompact K)
    (A : X → Matrix n n Real)
    (hAcont : ∀ i j, ContinuousOn (fun x ↦ A x i j) K)
    (hApos : ∀ x ∈ K, (A x).PosDef) :
    ∃ c : Real, 0 < c ∧ ∀ x ∈ K, ∀ v : Euc n,
      c * ‖v‖ ^ 2 ≤ _root_.Star.star v ⬝ᵥ A x *ᵥ v := by
  classical
  let e : Euc n →ₗ[Real] (n → Real) :=
    (PiLp.continuousLinearEquiv 2 Real (fun _ : n => Real)).toLinearMap
  let B : X → Euc n →L[Real] Euc n →L[Real] Real := fun x =>
    ((Matrix.toBilin' (A x)).comp e e).toContinuousBilinearMap
  have hB (x : X) (v w : Euc n) : B x v w = v ⬝ᵥ A x *ᵥ w := by
    simp only [B, LinearMap.toContinuousBilinearMap_apply,
      LinearMap.BilinForm.comp_apply, Matrix.toBilin'_apply']
    rfl
  let Q : X × Euc n → Real := fun p ↦
    ∑ i, ∑ j, A p.1 i j * p.2 i * p.2 j
  have hQcont : ContinuousOn Q (K ×ˢ (Set.univ : Set (Euc n))) := by
    refine continuousOn_finsetSum Finset.univ (fun i _ ↦ ?_)
    refine continuousOn_finsetSum Finset.univ (fun j _ ↦ ?_)
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact (hAcont i j).comp continuous_fst.continuousOn (fun p hp ↦ hp.1)
    · have hval : Continuous (fun v : Euc n => (v : n → Real)) :=
        (PiLp.continuousLinearEquiv 2 Real (fun _ : n ↦ Real)).continuous
      exact ((continuous_apply i).comp (hval.comp continuous_snd)).continuousOn
    · have hval : Continuous (fun v : Euc n => (v : n → Real)) :=
        (PiLp.continuousLinearEquiv 2 Real (fun _ : n ↦ Real)).continuous
      exact ((continuous_apply j).comp (hval.comp continuous_snd)).continuousOn
  have hBQ (p : X × Euc n) : B p.1 p.2 p.2 = Q p := by
    rw [hB]
    simp only [Q, dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hBc : ContinuousOn (fun p : X × Euc n => B p.1 p.2 p.2)
      (K ×ˢ (_root_.Set.univ : Set (Euc n))) := hQcont.congr fun p _ => hBQ p
  have hBp : ∀ x ∈ K, ∀ v : Euc n, v ≠ 0 → 0 < B x v v := by
    intro x hx v hv
    have hv' : (v : n → Real) ≠ 0 := by
      intro h
      exact hv (PiLp.ext fun i => congrFun h i)
    rw [hB]
    simpa only [Pi.star_apply, _root_.TrivialStar.star_trivial] using (hApos x hx).dotProduct_mulVec_pos hv'
  obtain ⟨c, hc, hbound⟩ := hBc.exists_uniform_bilin_quadratic_lower_bound hK hBp
  refine ⟨c, hc, ?_⟩
  intro x hx v
  have h := hbound x hx v
  rw [hB] at h
  simpa only [Pi.star_apply, _root_.TrivialStar.star_trivial] using h

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.exists_uniform_matrix_quadratic_lower_bound then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.exists_uniform_matrix_quadratic_lower_bound"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.exists_uniform_matrix_quadratic_lower_bound ``Submission.DifferentialGeometry.Analysis.Schauder.exists_uniform_matrix_quadratic_lower_bound

theorem exists_uniform_matrix_quadratic_lower_bound_of_finite
    {R X n : Type*} [Finite R] [TopologicalSpace X]
    [Fintype n]
    (K : R → Set X) (hK : ∀ r, IsCompact (K r))
    (A : R → X → Matrix n n Real)
    (hAcont : ∀ r i j, ContinuousOn (fun x ↦ A r x i j) (K r))
    (hApos : ∀ r x, x ∈ K r → (A r x).PosDef) :
    ∃ c : Real, 0 < c ∧ ∀ r x, x ∈ K r → ∀ v : Euc n,
      c * ‖v‖ ^ 2 ≤ _root_.Star.star v ⬝ᵥ A r x *ᵥ v := by
  classical
  have hlocal : ∀ r : R, ∃ c : Real, 0 < c ∧ ∀ x ∈ K r, ∀ v : Euc n,
      c * ‖v‖ ^ 2 ≤ _root_.Star.star v ⬝ᵥ A r x *ᵥ v := by
    intro r
    exact exists_uniform_matrix_quadratic_lower_bound
      (hK r) (A r) (hAcont r) (hApos r)
  choose c hcpos hcbound using hlocal
  cases isEmpty_or_nonempty R with
  | inl hR =>
      let := hR
      refine ⟨1, one_pos, ?_⟩
      intro r
      exact isEmptyElim r
  | inr hR =>
      let := hR
      let := Fintype.ofFinite R
      have himage : (Finset.univ.image c).Nonempty := by simp
      let cmin : Real := (Finset.univ.image c).min' himage
      have hcminmem : cmin ∈ Finset.univ.image c :=
        Finset.min'_mem (Finset.univ.image c) himage
      have hcminpos : 0 < cmin := by
        rcases Finset.mem_image.mp hcminmem with ⟨r, hr, hrc⟩
        rw [← hrc]
        exact hcpos r
      refine ⟨cmin, hcminpos, ?_⟩
      intro r x hx v
      exact (mul_le_mul_of_nonneg_right
        (Finset.min'_le (Finset.univ.image c) (c r)
          (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩))
        (sq_nonneg ‖v‖)).trans (hcbound r x hx v)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Schauder.exists_uniform_matrix_quadratic_lower_bound_of_finite then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Schauder.exists_uniform_matrix_quadratic_lower_bound_of_finite"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Schauder.exists_uniform_matrix_quadratic_lower_bound_of_finite ``Submission.DifferentialGeometry.Analysis.Schauder.exists_uniform_matrix_quadratic_lower_bound_of_finite

end DifferentialGeometry.Analysis.Schauder
