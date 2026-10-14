import Submission.DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarMetricControl

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

noncomputable section
open _root_.Set _root_.Submission.Set
open scoped _root_.Manifold _root_.Submission.Manifold _root_.ContDiff _root_.Topology _root_.Submission.Topology _root_.ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open _root_.Submission.DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem CylinderReference.axial_edist_le (C : CylinderReference) (p : Sphere 2) (a b : ℝ) :
    riemannianEDistOf (C.metric 0) (p, a) (p, b) ≤ ENNReal.ofReal |a - b| := by
  have hforward (a b : ℝ) (hab : a ≤ b) :
      riemannianEDistOf (C.metric 0) (p, a) (p, b) ≤ ENNReal.ofReal (b - a) := by
    have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) IC 1 (fun s : ℝ => (p, s)) (_root_.Set.Icc a b) :=
      contMDiffOn_const.prodMk contMDiffOn_id
    exact (edistOf_le_metricPathELength (C.metric 0) hab hcurve).trans
      (C.axial_metricPathELength_le p a b)
  rcases le_total a b with hab | hba
  · simpa only [abs_of_nonpos (sub_nonpos.mpr hab), neg_sub] using hforward a b hab
  · rw [riemannianEDistOf_comm]
    simpa only [abs_of_nonneg (sub_nonneg.mpr hba)] using hforward b a hba

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.axial_edist_le then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.axial_edist_le"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.axial_edist_le ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.CylinderReference.axial_edist_le

theorem exists_cylinderReference_axial_distance_error :
    ∃ D : ℝ, 0 < D ∧ ∀ (C : CylinderReference) (x y : Cylinder),
      |((riemannianEDistOf (C.metric 0) x y).toReal - |x.2 - y.2|)| ≤ D := by
  obtain ⟨B, hB, hpaths⟩ := exists_roundSphere_path_length_bound
  refine ⟨Real.sqrt 2 * B, mul_pos (Real.sqrt_pos.mpr (by norm_num)) hB, ?_⟩
  intro C x y
  obtain ⟨gamma, hg0, hg1, hg, hlen⟩ := hpaths x.1 y.1
  have htrans : riemannianEDistOf (C.metric 0) x (y.1, x.2) ≤
      ENNReal.ofReal (Real.sqrt 2 * B) := by
    have hcurve : ContMDiffOn 𝓘(ℝ, ℝ) IC 1 (fun s : ℝ => (gamma s, x.2)) (_root_.Set.Icc 0 1) :=
      hg.prodMk contMDiffOn_const
    have hh := edistOf_le_metricPathELength (C.metric 0) (by norm_num : (0 : ℝ) ≤ 1) hcurve
    rw [hg0, hg1] at hh
    exact hh.trans ((C.transverse_length_le x.2 hg).trans
      ((mul_le_mul' le_rfl hlen.le).trans_eq
        (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm))
  have hupper : riemannianEDistOf (C.metric 0) x y ≤
      ENNReal.ofReal (Real.sqrt 2 * B + |x.2 - y.2|) := by
    have hh := (riemannianEDistOf_triangle (C.metric 0) x (y.1, x.2) y).trans
      (add_le_add htrans (C.axial_edist_le y.1 x.2 y.2))
    simpa only [ENNReal.ofReal_add (mul_nonneg (Real.sqrt_nonneg _) hB.le) (abs_nonneg _)] using hh
  have hfin : riemannianEDistOf (C.metric 0) x y ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  have hlower := ENNReal.toReal_mono hfin (C.height_edist_le x y)
  rw [ENNReal.toReal_ofReal (abs_nonneg _)] at hlower
  have hupper' := ENNReal.toReal_le_of_le_ofReal
    (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) hB.le) (abs_nonneg _)) hupper
  rw [abs_le]
  constructor <;> linarith [mul_pos (Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)) hB]

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_cylinderReference_axial_distance_error then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_cylinderReference_axial_distance_error"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_cylinderReference_axial_distance_error ``Submission.DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn.exists_cylinderReference_axial_distance_error

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
