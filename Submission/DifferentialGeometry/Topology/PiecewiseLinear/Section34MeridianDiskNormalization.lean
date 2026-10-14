import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianNormalization
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34DisjointMeridianDisk

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open _root_.Classical in
theorem IsCylindricalDiagram.exists_cylinder_with_meridian
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space M.space)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1))
    (hdim : Module.finrank ℝ F = 3) {J : Set F} (hJ : IsPLSphere 1 J)
    (hJB : J ⊆ (boundaryComplex 3 M).space)
    (hnull : (⟨inclusion (hJB.trans (boundaryComplex_space_subset 3 M)),
      continuous_inclusion _⟩ : C(J, M.space)).Nullhomotopic)
    (hess : ¬ (⟨inclusion hJB, continuous_inclusion hJB⟩ :
      C(J, (boundaryComplex 3 M).space)).Nullhomotopic) :
    ∃ (g : E × ℝ → F) (q : (Fin 3 → ℝ) → F),
      IsCylindricalDiagram g D.space M.space ∧
      (∀ x ∈ D.space, g (x, 0) = g (x, 1)) ∧
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) (g '' (D.space ×ˢ {1 / 2})) ∧
      q '' stdSimplexBoundary 2 = J ∧ (g '' (D.space ×ˢ {1 / 2})) ⊆ M.space := by
  obtain ⟨r, hr, hpos⟩ := hf.exists_meridian_position D M hD hM hends hdim hJ hJB hnull hess
  obtain ⟨σ, hσ, hfinal, hdis⟩ := hpos.exists_disjoint_image D M hD hM hf hends hdim hr
  have hr01 : r ∈ _root_.Set.Ioo (0 : ℝ) 1 := by constructor <;> linarith [hr.1, hr.2]
  obtain ⟨f', hf', hslice, -, -⟩ := hf.exists_seam_rotation hD.isPolyhedron hends hr01
  have hends' : ∀ x ∈ D.space, f' (x, 0) = f' (x, 1) :=
    fun x hx => (hslice x hx).1.trans (hslice x hx).2.symm
  have hzero : f' '' (D.space ×ˢ ({0} : Set ℝ)) = f '' (D.space ×ˢ {r}) := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨(x, r), ⟨hx, rfl⟩, (hslice x hx).1.symm⟩
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have htr : t = r := ht
      subst t
      exact ⟨(x, 0), ⟨hx, rfl⟩, (hslice x hx).1⟩
  have hsideEq := hf'.image_side_eq_boundaryComplex D M hD hM hdim
  have hnewSide : σ '' J ⊆ f' '' ((boundaryComplex 2 D).space ×ˢ _root_.Set.Icc (0 : ℝ) 1) := by
    rw [hsideEq]
    exact hfinal.boundary
  have hnewEss : ¬ (⟨inclusion hnewSide, continuous_inclusion hnewSide⟩ :
      C(σ '' J, f' '' ((boundaryComplex 2 D).space ×ˢ _root_.Set.Icc (0 : ℝ) 1))).Nullhomotopic := by
    intro hn
    apply hfinal.boundaryEssential
    let e : C(f' '' ((boundaryComplex 2 D).space ×ˢ _root_.Set.Icc (0 : ℝ) 1),
        (boundaryComplex 3 M).space) := Homeomorph.setCongr hsideEq
    convert hn.comp_right e using 1
    ext x
    rfl
  obtain ⟨H, q, -, hg, hge, hq, hqJ, hsub⟩ :=
    hf'.exists_original_meridian_disk_of_disjoint_image D hD hends' hσ hJ
      (hJB.trans (boundaryComplex_space_subset 3 M)) hnewSide (hzero.symm ▸ hdis) hnewEss
  exact ⟨H ∘ f', q, hg, hge, hq, hqJ, hsub⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_cylinder_with_meridian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_cylinder_with_meridian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_cylinder_with_meridian ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_cylinder_with_meridian

end DifferentialGeometry.Topology.PiecewiseLinear
