import Submission.DifferentialGeometry.Topology.Manifold.BoundaryCollar.CurveUniqueness
import Submission.DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Manifold
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open scoped _root_.ContDiff
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.BoundaryCollar

private theorem time_le_of_boundary_flow_eq
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M] [T2Space M]
    {V : (y : M) → TangentSpace (𝓡∂ n) y}
    (hV : ContMDiff (𝓡∂ n) (𝓡∂ n).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ n) M)))
    {U : Set M} {ε : ℝ} {F : M × ℝ → M}
    (hzero : ∀ y ∈ U, F (y, 0) = y)
    (hcurve : ∀ y ∈ U, IsMIntegralCurveOn (fun t => F (y, t)) V (_root_.Set.Icc (0 : ℝ) ε))
    (hi : ∀ y ∈ U, ∀ t ∈ _root_.Set.Ioc (0 : ℝ) ε, (𝓡∂ n).IsInteriorPoint (F (y, t)))
    {p q : M} (hpU : p ∈ U) (hqU : q ∈ U) (hq : (𝓡∂ n).IsBoundaryPoint q)
    {t s : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) ε) (hs : s ∈ _root_.Set.Icc (0 : ℝ) ε)
    (he : F (p, t) = F (q, s)) : t ≤ s := by
  by_contra hn
  have hst : s < t := lt_of_not_ge hn
  have hqnot := ((𝓡∂ n).isBoundaryPoint_iff_not_isInteriorPoint q).mp hq
  by_cases hs0 : s = 0
  · rw [hs0, hzero q hqU] at he
    have hpint := hi p hpU t ⟨by linarith [hs.1], ht.2⟩
    rw [he] at hpint
    exact hqnot hpint
  · have hsp : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have hshift := ((hcurve p hpU).comp_add (t - s)).mono
      (show _root_.Set.Icc (0 : ℝ) s ⊆ {u | u + (t - s) ∈ _root_.Set.Icc (0 : ℝ) ε} from by
        intro u hu
        change 0 ≤ u + (t - s) ∧ u + (t - s) ≤ ε
        constructor <;> linarith [hu.1, hu.2, ht.2])
    have hfinal : ((fun u => F (p, u)) ∘ (fun u => u + (t - s))) s = F (q, s) := by
      change F (p, s + (t - s)) = F (q, s)
      rwa [show s + (t - s) = t by ring]
    have heq := isMIntegralCurveOn_Icc_unique_of_interior_of_eq_right hV hsp hshift
      ((hcurve q hqU).mono (_root_.Set.Icc_subset_Icc le_rfl hs.2))
      (fun u hu => hi p hpU (u + (t - s)) ⟨by linarith [hu.1], by linarith [hu.2, ht.2]⟩)
      hfinal
    have he0 := heq (show (0 : ℝ) ∈ _root_.Set.Icc (0 : ℝ) s from ⟨le_rfl, hsp.le⟩)
    change F (p, 0 + (t - s)) = F (q, 0) at he0
    rw [zero_add, hzero q hqU] at he0
    have hpint := hi p hpU (t - s) ⟨by linarith, by linarith [hs.1, ht.2]⟩
    rw [he0] at hpint
    exact hqnot hpint

run_cmd do
  let target := ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.time_le_of_boundary_flow_eq
  modify fun (state : Lean.Elab.Command.State) =>
    { state with scopes := state.scopes.map fun scope =>
      { scope with openDecls := .explicit `DifferentialGeometry.Manifold.BoundaryCollar.time_le_of_boundary_flow_eq target :: scope.openDecls } }

theorem boundary_flow_injective
    {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace n) M] [IsManifold (𝓡∂ n) ∞ M] [T2Space M]
    {V : (y : M) → TangentSpace (𝓡∂ n) y}
    (hV : ContMDiff (𝓡∂ n) (𝓡∂ n).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ n) M)))
    {U : Set M} (hKU : (𝓡∂ n).boundary M ⊆ U) {ε : ℝ} {F : M × ℝ → M}
    (hzero : ∀ y ∈ U, F (y, 0) = y)
    (hcurve : ∀ y ∈ U, IsMIntegralCurveOn (fun t => F (y, t)) V (_root_.Set.Icc (0 : ℝ) ε))
    (hi : ∀ y ∈ U, ∀ t ∈ _root_.Set.Ioc (0 : ℝ) ε, (𝓡∂ n).IsInteriorPoint (F (y, t))) :
    _root_.Function.Injective (fun q : BoundaryManifold (𝓡∂ n) M × _root_.Set.Icc (0 : ℝ) ε =>
      F ((q.1 : M), (q.2 : ℝ))) := by
  rintro ⟨p, t⟩ ⟨q, s⟩ he
  have hts : (t : ℝ) = s := le_antisymm
    (time_le_of_boundary_flow_eq hV hzero hcurve hi (hKU p.2) (hKU q.2) q.2 t.2 s.2 he)
    (time_le_of_boundary_flow_eq hV hzero hcurve hi (hKU q.2) (hKU p.2) p.2 s.2 t.2 he.symm)
  have hts' : t = s := Subtype.ext hts
  subst s
  have hpq : (p : M) = q := by
    by_cases ht0 : (t : ℝ) = 0
    · simpa only [ht0, hzero p (hKU p.2), hzero q (hKU q.2)] using he
    · have htp : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (Ne.symm ht0)
      have hsub : _root_.Set.Icc (0 : ℝ) t ⊆ _root_.Set.Icc (0 : ℝ) ε := _root_.Set.Icc_subset_Icc le_rfl t.2.2
      have heq := isMIntegralCurveOn_Icc_unique_of_interior_of_eq_right hV htp
        ((hcurve p (hKU p.2)).mono hsub) ((hcurve q (hKU q.2)).mono hsub)
        (fun s hs => hi p (hKU p.2) s ⟨hs.1, hs.2.le.trans t.2.2⟩) he
      simpa only [hzero p (hKU p.2), hzero q (hKU q.2)] using heq ⟨le_rfl, htp.le⟩
  exact Prod.ext (Subtype.ext hpq) rfl

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.boundary_flow_injective then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.boundary_flow_injective"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.boundary_flow_injective ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.boundary_flow_injective

end DifferentialGeometry.Manifold.BoundaryCollar
