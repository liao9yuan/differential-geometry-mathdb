import Submission.DifferentialGeometry.Topology.Manifold.BoundaryCollar.Diffeomorph
import Submission.DifferentialGeometry.Topology.Manifold.IntegralCurve.ScalarRate

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Function _root_.Manifold _root_.Topology _root_.TopologicalSpace
open scoped _root_.ContDiff
open _root_.Submission.DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.Manifold.BoundaryCollar


theorem exists_boundary_flow_collar_diffeomorph_height
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] (hK : IsCompact ((𝓡∂ (n + 1)).boundary M))
    {V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y}
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hpos : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M,
      0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p))
    {U : _root_.TopologicalSpace.Opens M} (hKU : (𝓡∂ (n + 1)).boundary M ⊆ U)
    {ε : ℝ} [Fact ((0 : ℝ) < ε)] {F : M × ℝ → M}
    (hF : ContMDiffOn ((𝓡∂ (n + 1)).prod 𝓘(ℝ, ℝ)) (𝓡∂ (n + 1)) ∞ F
      ((U : Set M) ×ˢ _root_.Set.Icc (0 : ℝ) ε))
    (hzero : ∀ q ∈ U, F (q, 0) = q)
    (hcurve : ∀ q ∈ U, IsMIntegralCurveOn (fun t => F (q, t)) V (_root_.Set.Icc (0 : ℝ) ε))
    (hi : ∀ q ∈ U, ∀ t ∈ _root_.Set.Ioc (0 : ℝ) ε, (𝓡∂ (n + 1)).IsInteriorPoint (F (q, t)))
    (N : _root_.TopologicalSpace.Opens M) (hKN : (𝓡∂ (n + 1)).boundary M ⊆ N)
    {r : M → ℝ} (hr : MDifferentiable (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r)
    (hrzero : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M, r p = 0)
    (hunit : ∀ y ∈ N, (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r y) (V y) = (1 : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < ε ∧
      let S : _root_.TopologicalSpace.Opens (BoundaryManifold (𝓡∂ (n + 1)) M × _root_.Set.Icc (0 : ℝ) ε) :=
        ⟨{q | (q.2 : ℝ) < δ},
          isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
      ∃ Y : _root_.TopologicalSpace.Opens M, (𝓡∂ (n + 1)).boundary M ⊆ Y ∧ Y ≤ N ∧
        ∃ d : Diffeomorph ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
          (𝓡∂ (n + 1)) S Y ∞,
          (∀ q : S, (d q : M) = F ((q.val.1 : M), (q.val.2 : ℝ))) ∧
          ∀ q : S, r (d q : M) = (q.val.2 : ℝ) := by
  obtain ⟨δ,hδ,hδε,Y,hKY,hYN,d,hd⟩ :=
    exists_boundary_flow_collar_diffeomorph hK hV hpos hKU hF hzero hcurve hi N hKN
  refine ⟨δ,hδ,hδε,Y,hKY,hYN,d,hd,?_⟩
  intro q
  let p := q.val.1
  let t : ℝ := q.val.2
  have ht : t ∈ _root_.Set.Icc (0 : ℝ) ε := q.val.2.property
  have htδ : t < δ := q.property
  have hsub : _root_.Set.Icc (0 : ℝ) t ⊆ _root_.Set.Icc (0 : ℝ) ε := _root_.Set.Icc_subset_Icc le_rfl ht.2
  have hinN : ∀ s ∈ _root_.Set.Icc (0 : ℝ) t, F ((p : M),s) ∈ N := by
    intro s hs
    let qs : {q : BoundaryManifold (𝓡∂ (n + 1)) M × _root_.Set.Icc (0 : ℝ) ε | (q.2 : ℝ) < δ} :=
      ⟨(p,⟨s,hsub hs⟩),hs.2.trans_lt htδ⟩
    have he : (d qs : M) = F ((p : M),s) := hd qs
    rw [← he]
    exact hYN (d qs).property
  have hh := scalar_eq_affine_of_integralCurve_constant_rate
    ((hcurve (p : M) (hKU p.property)).mono hsub) (convex_Icc (0 : ℝ) t)
    (a := 0) (k := 1) ⟨le_rfl,ht.1⟩ (fun s _ => hr (F ((p : M),s)))
    (fun s hs => hunit _ (hinN s hs)) ⟨ht.1,le_rfl⟩
  rw [hd]
  change r (F ((p : M),t)) = t
  change r (F ((p : M),t)) = r (F ((p : M),0)) + 1*(t-0) at hh
  simpa only [hzero (p : M) (hKU p.property),hrzero p,one_mul,sub_zero,zero_add] using hh

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.exists_boundary_flow_collar_diffeomorph_height then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.exists_boundary_flow_collar_diffeomorph_height"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.exists_boundary_flow_collar_diffeomorph_height ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.exists_boundary_flow_collar_diffeomorph_height


theorem exists_unit_height_boundary_collar
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] (hK : IsCompact ((𝓡∂ (n + 1)).boundary M))
    {V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y}
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hpos : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M,
      0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p))
    (N : _root_.TopologicalSpace.Opens M) (hKN : (𝓡∂ (n + 1)).boundary M ⊆ N)
    {r : M → ℝ} (hr : MDifferentiable (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r)
    (hrzero : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M, r p = 0)
    (hunit : ∀ y ∈ N, (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r y) (V y) = (1 : ℝ)) :
    ∃ (ε : ℝ) (hε : 0 < ε),
      let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
      ∃ (δ : ℝ) (hδ : 0 < δ), δ < ε ∧
        let S : _root_.TopologicalSpace.Opens (BoundaryManifold (𝓡∂ (n + 1)) M × _root_.Set.Icc (0 : ℝ) ε) :=
          ⟨{q | (q.2 : ℝ) < δ},
            isOpen_lt (continuous_subtype_val.comp continuous_snd) continuous_const⟩
        ∃ Y : _root_.TopologicalSpace.Opens M, (𝓡∂ (n + 1)).boundary M ⊆ Y ∧ Y ≤ N ∧
          ∃ d : Diffeomorph ((HasSmoothBoundary.boundaryModel (𝓡∂ (n + 1))).prod (𝓡∂ 1))
            (𝓡∂ (n + 1)) S Y ∞,
            (∀ p, (d ⟨(p, ⟨0, ⟨le_rfl, hε.le⟩⟩), hδ⟩ : M) =
              boundaryInclusion (𝓡∂ (n + 1)) M p) ∧
            ∀ q : S, r (d q : M) = (q.val.2 : ℝ) := by
  obtain ⟨U,hKU,ε,hε,F,hF,hzero,hcurve,hi,_⟩ :=
    exists_uniform_boundary_flow_of_inward hV hpos hK
  refine ⟨ε,hε,?_⟩
  let : Fact ((0 : ℝ) < ε) := ⟨hε⟩
  obtain ⟨δ,hδ,hδε,Y,hKY,hYN,d,hd,hheight⟩ :=
    exists_boundary_flow_collar_diffeomorph_height hK hV hpos hKU hF hzero hcurve hi N hKN hr hrzero hunit
  refine ⟨δ,hδ,hδε,Y,hKY,hYN,d,?_,hheight⟩
  intro p
  rw [hd]
  exact hzero p.val (hKU p.property)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Manifold.BoundaryCollar.exists_unit_height_boundary_collar then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Manifold.BoundaryCollar.exists_unit_height_boundary_collar"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Manifold.BoundaryCollar.exists_unit_height_boundary_collar ``Submission.DifferentialGeometry.Manifold.BoundaryCollar.exists_unit_height_boundary_collar

end DifferentialGeometry.Manifold.BoundaryCollar
