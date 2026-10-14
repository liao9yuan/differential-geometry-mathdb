import Submission.DifferentialGeometry.Geometry.Connection.AlongCurve

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Bundle _root_.Set
open scoped _root_.Manifold _root_.ContDiff

namespace CovariantDerivative
open _root_.CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 1 F V I]

open _root_.CovariantDerivative in
structure IsParallelSet (cov : CovariantDerivative I F V) (K : Set (_root_.Bundle.TotalSpace F V)) : Prop where
  mem_of_parallel : ∀ {a b t₀ : ℝ} {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)},
    t₀ ∈ _root_.Set.Icc a b → ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (_root_.Set.Icc a b) →
    MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : _root_.Bundle.TotalSpace F V)) (_root_.Set.Icc a b) →
    (∀ t ∈ _root_.Set.Icc a b, cov.derivAlongWithin γ Z (_root_.Set.Icc a b) t = 0) →
    (⟨γ t₀, Z t₀⟩ : _root_.Bundle.TotalSpace F V) ∈ K →
    ∀ t ∈ _root_.Set.Icc a b, (⟨γ t, Z t⟩ : _root_.Bundle.TotalSpace F V) ∈ K

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.IsParallelSet then
    throwError "Refusing to shadow existing declaration CovariantDerivative.IsParallelSet"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.IsParallelSet ``Submission.CovariantDerivative.IsParallelSet

theorem IsParallelSet.mem_iff_of_parallel {cov : CovariantDerivative I F V}
    {K : Set (_root_.Bundle.TotalSpace F V)} (hK : cov.IsParallelSet K)
    {a b t₀ t : ℝ} {γ : ℝ → M} {Z : ∀ t : ℝ, V (γ t)}
    (ht₀ : t₀ ∈ _root_.Set.Icc a b) (ht : t ∈ _root_.Set.Icc a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (_root_.Set.Icc a b))
    (hZ : MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, Z t⟩ : _root_.Bundle.TotalSpace F V)) (_root_.Set.Icc a b))
    (hZpar : ∀ t ∈ _root_.Set.Icc a b, cov.derivAlongWithin γ Z (_root_.Set.Icc a b) t = 0) :
    (⟨γ t, Z t⟩ : _root_.Bundle.TotalSpace F V) ∈ K ↔
      (⟨γ t₀, Z t₀⟩ : _root_.Bundle.TotalSpace F V) ∈ K :=
  ⟨fun h => hK.mem_of_parallel ht hγ hZ hZpar h t₀ ht₀,
    fun h => hK.mem_of_parallel ht₀ hγ hZ hZpar h t ht⟩

run_cmd do
  Lean.modifyEnv fun env => env.registerNamespace `Submission.CovariantDerivative.IsParallelSet
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.IsParallelSet.mem_iff_of_parallel then
    throwError "Refusing to shadow existing declaration CovariantDerivative.IsParallelSet.mem_iff_of_parallel"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.IsParallelSet.mem_iff_of_parallel ``Submission.CovariantDerivative.IsParallelSet.mem_iff_of_parallel

theorem IsParallelSet.image_eq_of_parallel {cov : CovariantDerivative I F V}
    {K : Set (_root_.Bundle.TotalSpace F V)} (hK : cov.IsParallelSet K)
    {a b t₀ : ℝ} {γ : ℝ → M} (ht₀ : t₀ ∈ _root_.Set.Icc a b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (_root_.Set.Icc a b))
    (T : ∀ t : ℝ, V (γ t₀) ≃L[ℝ] V (γ t))
    (hT₀ : ∀ v, T t₀ v = v)
    (hT : ∀ v, MDifferentiableOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, F))
      (fun t => (⟨γ t, T t v⟩ : _root_.Bundle.TotalSpace F V)) (_root_.Set.Icc a b))
    (hTpar : ∀ v t, t ∈ _root_.Set.Icc a b →
      cov.derivAlongWithin γ (fun s => T s v) (_root_.Set.Icc a b) t = 0)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc a b) :
    T t '' {v : V (γ t₀) | (⟨γ t₀, v⟩ : _root_.Bundle.TotalSpace F V) ∈ K} =
      {v : V (γ t) | (⟨γ t, v⟩ : _root_.Bundle.TotalSpace F V) ∈ K} := by
  have hmem (v : V (γ t₀)) :=
    hK.mem_iff_of_parallel ht₀ ht hγ (hT v) (hTpar v)
  simp only [hT₀] at hmem
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (hmem w).mpr hw
  · intro hv
    refine ⟨(T t).symm v, ?_, (T t).apply_symm_apply v⟩
    exact (hmem ((T t).symm v)).mp (by simpa only [(T t).apply_symm_apply, _root_.Set.mem_ofPred_eq] using hv)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `CovariantDerivative.IsParallelSet.image_eq_of_parallel then
    throwError "Refusing to shadow existing declaration CovariantDerivative.IsParallelSet.image_eq_of_parallel"
  Lean.modifyEnv fun env => Lean.addAlias env `CovariantDerivative.IsParallelSet.image_eq_of_parallel ``Submission.CovariantDerivative.IsParallelSet.image_eq_of_parallel

end CovariantDerivative
