import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34MeridianDiskNormalization
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.CylindricalMeridian

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open _root_.Classical in
theorem IsCylindricalDiagram.slice_chart_rim_eq
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {f : E × ℝ → F} {S : Set F} (hf : IsCylindricalDiagram f D.space S)
    {t : ℝ} (ht : t ∈ _root_.Set.Icc (0 : ℝ) 1) {q : (Fin 3 → ℝ) → F}
    (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) (f '' (D.space ×ˢ {t}))) :
    q '' stdSimplexBoundary 2 = f '' ((boundaryComplex 2 D).space ×ˢ {t}) := by
  obtain ⟨d, hd⟩ := hD
  have hdBd := hd.image_stdSimplexBoundary_eq_boundaryComplex D rfl
  let p : (Fin 3 → ℝ) → F := fun x => f (d x, t)
  have hp : IsPLHomeomorphOn p (stdSimplex ℝ (Fin 3)) (f '' (D.space ×ˢ {t})) :=
    hd.trans (hf.isPLHomeomorphOn_slice (isPolyhedron_space D) ht)
  obtain ⟨K, hKfin, hKspace⟩ := (IsPLBall.isPolyhedron ⟨q, hq⟩).exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  have hqp : q '' stdSimplexBoundary 2 = p '' stdSimplexBoundary 2 := by
    rw [hq.image_stdSimplexBoundary_eq_boundaryComplex K hKspace,
      hp.image_stdSimplexBoundary_eq_boundaryComplex K hKspace]
  rw [hqp, ← hdBd, _root_.Set.prod_singleton, _root_.Set.image_image, _root_.Set.image_image]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.slice_chart_rim_eq then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.slice_chart_rim_eq"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.slice_chart_rim_eq ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.slice_chart_rim_eq

open _root_.Classical in
theorem IsCylindricalDiagram.exists_rotation_with_prescribed_meridian
    (D : Geometry.SimplicialComplex ℝ E) [Finite D.faces] (hD : IsPLBall 2 D.space)
    {f : E × ℝ → F} {S J : Set F} (hf : IsCylindricalDiagram f D.space S)
    (hends : ∀ x ∈ D.space, f (x, 0) = f (x, 1)) {t : ℝ} (ht : t ∈ _root_.Set.Ioo (0 : ℝ) 1)
    {q : (Fin 3 → ℝ) → F}
    (hq : IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) (f '' (D.space ×ˢ {t})))
    (hqJ : q '' stdSimplexBoundary 2 = J) :
    ∃ g : E × ℝ → F, IsCylindricalDiagram g D.space S ∧
      (∀ x ∈ D.space, g (x, 0) = g (x, 1)) ∧
      IsPLHomeomorphOn q (stdSimplex ℝ (Fin 3)) (g '' (D.space ×ˢ {0})) ∧
      g '' ((boundaryComplex 2 D).space ×ˢ {0}) = J ∧
      g '' (D.space ×ˢ {0}) = f '' (D.space ×ˢ {t}) := by
  obtain ⟨g, hg, hcap, -, -⟩ := hf.exists_seam_rotation hD.isPolyhedron hends ht
  have hzero : g '' (D.space ×ˢ ({0} : Set ℝ)) = f '' (D.space ×ˢ {t}) := by
    rw [_root_.Set.prod_singleton, _root_.Set.prod_singleton, _root_.Set.image_image, _root_.Set.image_image]
    apply _root_.Set.image_congr
    intro x hx
    exact (hcap x hx).1
  have hqg := hzero.symm ▸ hq
  exact ⟨g, hg, fun x hx => (hcap x hx).1.trans (hcap x hx).2.symm, hqg,
    (hg.slice_chart_rim_eq D hD (by norm_num) hqg).symm.trans hqJ, hzero⟩

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_rotation_with_prescribed_meridian then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_rotation_with_prescribed_meridian"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_rotation_with_prescribed_meridian ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_rotation_with_prescribed_meridian

open _root_.Classical in
theorem IsCylindricalDiagram.exists_unique_basepoint_of_singleton_seam
    (D : Geometry.SimplicialComplex ℝ E) (M : Geometry.SimplicialComplex ℝ F)
    [Finite D.faces] [Finite M.faces] (hD : IsPLBall 2 D.space)
    (hM : IsCombinatorialManifoldWithBoundary 3 M) (hdim : Module.finrank ℝ F = 3)
    {f : E × ℝ → F} (hf : IsCylindricalDiagram f D.space M.space)
    {J L : Set F} {p : F} (hLB : L ⊆ (boundaryComplex 3 M).space)
    (hJ : f '' ((boundaryComplex 2 D).space ×ˢ ({0} : Set ℝ)) = J)
    (htrace : L ∩ J = {p}) :
    L ∩ f '' (D.space ×ˢ ({0} : Set ℝ)) = {p} ∧
      ∃! x, x ∈ (boundaryComplex 2 D).space ∧ f (x, 0) = p := by
  have hfull := hf.meridian_trace_eq_rim_trace D M hD hM hdim hLB
    (show (0 : ℝ) ∈ _root_.Set.Icc 0 1 by norm_num)
  refine ⟨hfull.trans ((congrArg (L ∩ ·) hJ).trans htrace), ?_⟩
  have hpJ : p ∈ J := (htrace.symm.subset rfl).2
  obtain ⟨⟨x, t⟩, ⟨hx, ht⟩, heq⟩ := hJ.symm.subset hpJ
  have ht0 : t = 0 := ht
  subst t
  refine ⟨x, ⟨hx, heq⟩, ?_⟩
  intro y hy
  exact (hf.isPLHomeomorphOn_slice hD.isPolyhedron (by norm_num)).bijOn.injOn
    (boundaryComplex_space_subset 2 D hy.1) (boundaryComplex_space_subset 2 D hx)
    (hy.2.trans heq.symm)

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_unique_basepoint_of_singleton_seam then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_unique_basepoint_of_singleton_seam"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_unique_basepoint_of_singleton_seam ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsCylindricalDiagram.exists_unique_basepoint_of_singleton_seam

end DifferentialGeometry.Topology.PiecewiseLinear
