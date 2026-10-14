import Submission.DifferentialGeometry.Geometry.Operator.Laplacian.Rough

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission
open _root_.Submission.DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

open _root_.Submission.DifferentialGeometry.Geometry.Operator
namespace DifferentialGeometry.Tensor.RSTensor

noncomputable section

open _root_.Bundle _root_.Submission.Bundle _root_.Submission.DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold _root_.ContDiff _root_.BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {Hm : Type*} [TopologicalSpace Hm]
variable {I : ModelWithCorners Real E Hm}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Hm M] [IsManifold I ∞ M]

theorem trace_eq_line_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : SmoothRiemannianMetric I M)
    {x : M}
    (Z : TangentSpace I x)
    (V : ι → TangentSpace I x)
    (H :
      Tensor0SSpace
        (𝕜 := Real) (E := E) (H := Hm)
        (I := I) (M := M) 2 x)
    (hZ : 0 < g.inner x Z Z)
    (hperp : ∀ i, g.inner x Z (V i) = 0)
    (hLI : LinearIndependent Real V)
    (hcard :
      Fintype.card ι = Module.finrank Real E - 1) :
    let G : Matrix ι ι Real :=
      Matrix.of fun i j => g.inner x (V i) (V j)
    let A : Matrix ι ι Real :=
      Matrix.of fun i j =>
        H (vec2 (I := I) (V i) (V j))
    metricTracePair0SAt (I := I) g H
      =
        (g.inner x Z Z)⁻¹ *
          H (vec2 (I := I) Z Z)
        + Matrix.trace (G⁻¹ * A) := by
  classical
  dsimp only
  let G : Matrix ι ι Real :=
    Matrix.of fun i j => g.inner x (V i) (V j)
  let A : Matrix ι ι Real :=
    Matrix.of fun i j => H (vec2 (I := I) (V i) (V j))
  let W : Option ι → TangentSpace I x :=
    fun o => Option.casesOn' o Z V
  let φ : TangentSpace I x →ₗ[Real] Real := (g.inner x Z).toLinearMap
  have hVker : Set.range V ⊆ LinearMap.ker φ := by
    rintro y ⟨i, rfl⟩
    change g.inner x Z (V i) = 0
    exact hperp i
  have hZspan : Z ∉ Submodule.span Real (Set.range V) := by
    intro hmem
    have hker : Z ∈ LinearMap.ker φ :=
      (Submodule.span_le.2 hVker) hmem
    have hzero : g.inner x Z Z = 0 := hker
    exact hZ.ne' hzero
  have hWLI : LinearIndependent Real W := by
    simpa only [W] using hLI.option hZspan
  have hZne : Z ≠ 0 := by
    intro h
    subst Z
    simp at hZ
  have hdim : 0 < Module.finrank Real E := by
    exact Module.finrank_pos_iff.mpr ⟨Z, 0, hZne⟩
  have hcardW :
      Fintype.card (Option ι) =
        Module.finrank Real (TangentSpace I x) := by
    rw [Fintype.card_option, hcard]
    exact Nat.succ_pred_eq_of_pos hdim
  let b : Module.Basis (Option ι) Real (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank hWLI hcardW
  have hb (o : Option ι) : b o = W o := by
    exact congrFun
      (coe_basisOfLinearIndependentOfCardEqFinrank hWLI hcardW) o
  have hb0 : b _root_.Option.none = Z := by
    exact (hb _root_.Option.none).trans (by rfl)
  have hbs (i : ι) : b (_root_.Option.some i) = V i := by
    exact (hb (_root_.Option.some i)).trans (by rfl)
  let q : Option ι → Option ι → Real :=
    basisInvMetric (I := I) g x b
  have hq :
      MetricInverseInBasis (I := I) g x b q := by
    simpa only [q] using basisInvMetric_isInverse (I := I) g x b
  have hqsymm (i j : Option ι) : q i j = q j i := by
    simpa only [q] using basisInvMetric_symm (I := I) g x b i j
  have hperp' (i : ι) : g.inner x (V i) Z = 0 := by
    rw [g.symm x (V i) Z]
    exact hperp i
  have hq00mul :
      q _root_.Option.none _root_.Option.none * g.inner x Z Z = 1 := by
    have h := (hq _root_.Option.none _root_.Option.none).1
    simpa only [Fintype.sum_option, hb0, hbs, hperp', _root_.MulZeroClass.mul_zero,
      Finset.sum_const_zero, add_zero, if_pos] using h
  have hq00 :
      q _root_.Option.none _root_.Option.none = (g.inner x Z Z)⁻¹ :=
    eq_inv_of_mul_eq_one_left hq00mul
  have hq0s (j : ι) : q _root_.Option.none (_root_.Option.some j) = 0 := by
    have h := (hq _root_.Option.none (_root_.Option.some j)).2
    have hne : (_root_.Option.none : Option ι) ≠ _root_.Option.some j := by simp
    have hmul : g.inner x Z Z * q _root_.Option.none (_root_.Option.some j) = 0 := by
      simpa only [Fintype.sum_option, hb0, hbs, hperp, _root_.MulZeroClass.zero_mul,
        Finset.sum_const_zero, add_zero, if_neg hne] using h
    exact (mul_eq_zero.mp hmul).resolve_left hZ.ne'
  have hqs0 (i : ι) : q (_root_.Option.some i) _root_.Option.none = 0 := by
    rw [hqsymm (_root_.Option.some i) _root_.Option.none, hq0s]
  let Q : Matrix ι ι Real := fun i j => q (_root_.Option.some i) (_root_.Option.some j)
  have hQG : Q * G = 1 := by
    ext i j
    change (∑ k, Q i k * G k j) = if i = j then 1 else 0
    have h := (hq (_root_.Option.some i) (_root_.Option.some j)).1
    simpa only [Q, G, Matrix.of_apply,
      Fintype.sum_option, hb0, hbs, hperp, _root_.MulZeroClass.mul_zero, zero_add,
      Option.some.injEq] using h
  have hGinv : G⁻¹ = Q :=
    Matrix.inv_eq_left_inv hQG
  have hqss (i j : ι) : q (_root_.Option.some i) (_root_.Option.some j) = G⁻¹ i j := by
    rw [hGinv]
  have hGsymm (i j : ι) : G⁻¹ i j = G⁻¹ j i := by
    rw [hGinv]
    exact hqsymm (_root_.Option.some i) (_root_.Option.some j)
  have hsum :
      (∑ i : ι, ∑ j : ι,
          G⁻¹ i j * H (vec2 (I := I) (V i) (V j))) =
        Matrix.trace (G⁻¹ * A) := by
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.mul_apply, A, Matrix.of_apply]
    calc
      (∑ i : ι, ∑ j : ι,
          G⁻¹ i j * H (vec2 (I := I) (V i) (V j))) =
          ∑ i : ι, ∑ j : ι,
            G⁻¹ j i * H (vec2 (I := I) (V i) (V j)) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              rw [hGsymm i j]
      _ = ∑ j : ι, ∑ i : ι,
            G⁻¹ j i * H (vec2 (I := I) (V i) (V j)) := by
              rw [Finset.sum_comm]
  rw [metricTracePair0SAt_eq_sum_basis (I := I) g b q hq H]
  rw [Fintype.sum_option]
  simp only [Fintype.sum_option, hb0, hbs, hq00, hq0s, hqs0, hqss,
    _root_.MulZeroClass.zero_mul, Finset.sum_const_zero, add_zero, zero_add]
  simpa only [G, A] using congrArg
    (fun r => (g.inner x Z Z)⁻¹ * H (vec2 (I := I) Z Z) + r) hsum

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Tensor.RSTensor.trace_eq_line_add then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Tensor.RSTensor.trace_eq_line_add"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Tensor.RSTensor.trace_eq_line_add ``Submission.DifferentialGeometry.Tensor.RSTensor.trace_eq_line_add

end

end DifferentialGeometry.Tensor.RSTensor
