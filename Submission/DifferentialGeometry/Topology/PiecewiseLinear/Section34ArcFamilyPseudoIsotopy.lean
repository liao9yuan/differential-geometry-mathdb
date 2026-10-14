import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CircleAnnulusIsotopy
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.FiniteGluing

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_PL_arc_family_pseudoisotopy
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [Finite ι] {A : ι → Set E} {γ : ι → ℝ → E}
    (hγ : ∀ i, IsPLHomeomorphOn (γ i) (_root_.Set.Icc 0 1) (A i))
    (hinter : ∀ i j, i ≠ j → A i ∩ A j ⊆ {γ i 0, γ i 1})
    {u : E → E} (hu : ∀ i, IsPLHomeomorphOn u (A i) (A i))
    (hzero : ∀ i, u (γ i 0) = γ i 0) (hone : ∀ i, u (γ i 1) = γ i 1) :
    ∃ Φ : E × ℝ → E × ℝ,
      IsPLHomeomorphOn Φ ((⋃ i, A i) ×ˢ _root_.Set.Icc (0 : ℝ) 1)
        ((⋃ i, A i) ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      (∀ x ∈ ⋃ i, A i, Φ (x, 0) = (x, 0)) ∧
      (∀ x ∈ ⋃ i, A i, Φ (x, 1) = (u x, 1)) ∧
      (∀ i, Φ '' (A i ×ˢ _root_.Set.Icc (0 : ℝ) 1) = A i ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∧
      ∀ i, ∀ t ∈ _root_.Set.Icc (0 : ℝ) 1,
        Φ (γ i 0, t) = (γ i 0, t) ∧ Φ (γ i 1, t) = (γ i 1, t) := by
  choose Ψ hΨ hΨ0 hΨ1 hΨleft hΨright using fun i =>
    exists_isPLHomeomorphOn_arc_prod_of_fixed_endpoints (hγ i) (hu i) (hzero i) (hone i)
  have hpoly (i : ι) : IsPolyhedron (A i ×ˢ _root_.Set.Icc (0 : ℝ) 1) :=
    ((isPLBall_Icc zero_lt_one).of_isPLHomeomorphOn (hγ i)).isPolyhedron.prod
      isHPolytope_Icc.isPolyhedron
  have hfix (i j : ι) (hij : i ≠ j) : _root_.Set.EqOn (Ψ i) id
      ((A i ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ (A j ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
    rintro ⟨x, t⟩ ⟨⟨hxi, ht⟩, hxj, -⟩
    rcases hinter i j hij ⟨hxi, hxj⟩ with hx | hx
    · change x = γ i 0 at hx
      simpa only [hx, id_eq] using hΨleft i t ht
    · change x = γ i 1 at hx
      simpa only [hx, id_eq] using hΨright i t ht
  have hcompat (i j : ι) : _root_.Set.EqOn (Ψ i) (Ψ j)
      ((A i ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ (A j ×ˢ _root_.Set.Icc (0 : ℝ) 1)) := by
    rcases eq_or_ne i j with rfl | hij
    · exact fun _ _ => rfl
    · exact fun _ hx => (hfix i j hij hx).trans (hfix j i hij.symm ⟨hx.2, hx.1⟩).symm
  have hmeet (i j : ι) :
      Ψ i '' ((A i ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ (A j ×ˢ _root_.Set.Icc (0 : ℝ) 1)) =
        (A i ×ˢ _root_.Set.Icc (0 : ℝ) 1) ∩ (A j ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    rcases eq_or_ne i j with rfl | hij
    · rw [_root_.Set.inter_self]
      exact (hΨ i).image_eq
    · exact (hfix i j hij).image_eq.trans (_root_.Set.image_id _)
  obtain ⟨Φ, hΦ, hΦi⟩ := exists_isPLHomeomorphOn_iUnion hpoly hΨ hcompat hmeet
  rw [← _root_.Set.iUnion_prod_const] at hΦ
  refine ⟨Φ, hΦ, ?_, ?_, fun i => (hΦi i).image_eq.trans (hΨ i).image_eq, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (hΦi i ⟨hi, by norm_num⟩).trans (hΨ0 i x hi)
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact (hΦi i ⟨hi, by norm_num⟩).trans (hΨ1 i x hi)
  · intro i t ht
    exact ⟨(hΦi i ⟨(hγ i).bijOn.mapsTo (by norm_num), ht⟩).trans (hΨleft i t ht),
      (hΦi i ⟨(hγ i).bijOn.mapsTo (by norm_num), ht⟩).trans (hΨright i t ht)⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.exists_PL_arc_family_pseudoisotopy then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.exists_PL_arc_family_pseudoisotopy"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.exists_PL_arc_family_pseudoisotopy ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.exists_PL_arc_family_pseudoisotopy

end DifferentialGeometry.Topology.PiecewiseLinear
