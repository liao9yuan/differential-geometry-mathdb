import Submission.DifferentialGeometry.Geometry.Metric.TensorInner.FiberNorm.SlotCurry.Defs

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section


open _root_.Bundle _root_.Submission.Bundle _root_.Manifold _root_.Set
open scoped _root_.Manifold _root_.Topology _root_.ContDiff _root_.BigOperators _root_.RealInnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Elliptic

open _root_.Submission.DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J)
    (hreprSucc : ∀ S : TensorRSSpace 0 (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (s + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) S n e K J)
    (T : TensorRSSpace 0 (s + 1) I x) :
    riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T =
      ∑ a : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
          (slot0Curry (I := I) (M := M) g x s e K₀ T a) := by
  classical
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x (s + 1) e
    hreprSucc T K₀]
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (s + 1) => Fin n))
        (fun (pr : Fin n × (Fin s → Fin n)) =>
          (fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) T n e K₀
            (Fin.cons pr.1 pr.2)) ^ 2)
        (fun J : Fin (s + 1) → Fin n =>
          (fiberNormSqComponent (I := I) (M := M) g x 0 (s + 1) T n e K₀ J) ^ 2)
        (fun pr => by simp [Fin.consEquiv])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [riemannianFiberNormSq_eq_sum_componentS_sq (I := I) (M := M) g x s e hreprS
        (slot0Curry (I := I) (M := M) g x s e K₀ T a) K₀]
  refine Finset.sum_congr rfl (fun J' _ => ?_)
  rw [fiberNormSqComponent_slot0Curry (I := I) (M := M) g x s e K₀ T a J']

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame

theorem riemannianFiberNormSq_slot0Curry_le_of_frame
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    {n : ℕ} (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n)
    (hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J)
    (hreprSucc : ∀ S : TensorRSSpace 0 (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (s + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) S n e K J)
    (T : TensorRSSpace 0 (s + 1) I x) (a : Fin n) :
    riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (slot0Curry (I := I) (M := M) g x s e K₀ T a) ≤
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T := by
  classical
  rw [riemannianFiberNormSq_succ_eq_sum_slot0Curry_of_frame (I := I) (M := M) g s x e K₀
    hreprS hreprSucc T]
  refine Finset.single_le_sum (f := fun a : Fin n =>
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (slot0Curry (I := I) (M := M) g x s e K₀ T a))
    (fun b _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _)
    (Finset.mem_univ a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_slot0Curry_le_of_frame then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_slot0Curry_le_of_frame"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_slot0Curry_le_of_frame ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_slot0Curry_le_of_frame

theorem riemannianFiberNormSq_slot0Curry_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 (s + 1) I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      ∀ a : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (slot0Curry (I := I) (M := M) g x s e K₀ T a) ≤
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T := by
  classical
  obtain ⟨n, e, K₀, hn, hsum⟩ :=
    riemannianFiberNormSq_succ_eq_sum_slot0Curry (I := I) (M := M) g s x T
  refine ⟨n, e, K₀, hn, fun a => ?_⟩
  rw [hsum]
  refine Finset.single_le_sum (f := fun a : Fin n =>
      riemannianFiberNormSq (I := I) (M := M) g 0 s x
        (slot0Curry (I := I) (M := M) g x s e K₀ T a))
    (fun b _ => riemannianFiberNormSq_nonneg (I := I) (M := M) g 0 s x _)
    (Finset.mem_univ a)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_slot0Curry_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_slot0Curry_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_slot0Curry_le ``Submission.DifferentialGeometry.Analysis.Elliptic.riemannianFiberNormSq_slot0Curry_le

theorem exists_riemannianFiberNormSq_slot0Curry_le
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (T : TensorRSSpace 0 (s + 1) I x) :
    ∃ (n : ℕ) (e : Fin n → TangentSpace I x) (K₀ : Fin 0 → Fin n),
      n = Module.finrank ℝ (TangentSpace I x) ∧
      (∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0) ∧
      ∀ a : Fin n,
        riemannianFiberNormSq (I := I) (M := M) g 0 s x
            (slot0Curry (I := I) (M := M) g x s e K₀ T a) ≤
          riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x T := by
  classical
  let cd : InnerProductSpace.Core ℝ (TangentSpace I x) := g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x => cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded ℝ {v : TangentSpace I x |
      RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  let nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  let ips : InnerProductSpace ℝ (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  set n : ℕ := Module.finrank ℝ (TangentSpace I x) with hn_def
  set eob : OrthonormalBasis (Fin n) ℝ (TangentSpace I x) := stdOrthonormalBasis ℝ _
    with heob_def
  set e : Fin n → TangentSpace I x := fun i => eob i with he_def
  have hinner_eq : ∀ u v : TangentSpace I x, (_root_.Inner.inner ℝ u v : ℝ) = g.inner x u v :=
    fun u v => rfl
  have horth : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    have horthb : Orthonormal ℝ (fun i : Fin n => eob i) := eob.orthonormal
    have hite := (orthonormal_iff_ite (𝕜 := ℝ) (E := TangentSpace I x)).mp horthb i j
    rw [he_def, ← hinner_eq (eob i) (eob j)]
    exact hite
  refine ⟨n, e, fun k => k.elim0, hn_def, horth, fun a => ?_⟩
  set K₀ : Fin 0 → Fin n := fun k => k.elim0 with hK₀
  have hreprSucc : ∀ S : TensorRSSpace 0 (s + 1) I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 (s + 1) x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin (s + 1) → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 (s + 1) S n e K J := by
    intro S; rfl
  have hreprS : ∀ S : TensorRSSpace 0 s I x,
      riemannianFiberNormSq (I := I) (M := M) g 0 s x S =
        ∑ K : Fin 0 → Fin n, ∑ J : Fin s → Fin n,
          fiberNormSqSummand (I := I) (M := M) g x 0 s S n e K J := by
    intro S; rfl
  exact riemannianFiberNormSq_slot0Curry_le_of_frame (I := I) (M := M) g s x e K₀
    hreprS hreprSucc T a

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Analysis.Elliptic.exists_riemannianFiberNormSq_slot0Curry_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Analysis.Elliptic.exists_riemannianFiberNormSq_slot0Curry_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Analysis.Elliptic.exists_riemannianFiberNormSq_slot0Curry_le ``Submission.DifferentialGeometry.Analysis.Elliptic.exists_riemannianFiberNormSq_slot0Curry_le

end Elliptic
end Analysis
end DifferentialGeometry
