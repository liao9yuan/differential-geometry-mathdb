import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34FillingLongitudes
import Submission.DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularFillingInTubeModel
import Submission.DifferentialGeometry.Topology.FundamentalGroup.Nullhomotopy

-- MathDB adaptation: helper modules, namespaces, and references relocated into Submission.
-- Preserve the upstream library elaboration options in a source-only submission.
set_option autoImplicit false
set_option maxSynthPendingDepth 3

namespace Submission

open _root_.Set _root_.Submission.DifferentialGeometry.Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem CarriesFundamentalGroupOnto.not_nullhomotopic_inclusion_in_solid_torus
    {X : Type*} [TopologicalSpace X] {J S : Set X}
    (hcarry : CarriesFundamentalGroupOnto J S) (hJ : J.Nonempty)
    (hS : IsTopologicalSolidTorus S) (hJS : J ⊆ S) :
    ¬ (⟨inclusion hJS, continuous_inclusion hJS⟩ : C(J, S)).Nullhomotopic := by
  intro hn
  obtain ⟨x, hx⟩ := hJ
  let i : C(J, S) := ⟨inclusion hJS, continuous_inclusion hJS⟩
  let e := hS.fundamentalGroupEquivInt (i ⟨x, hx⟩)
  obtain ⟨a, ha⟩ := hcarry.2 hJS ⟨x, hx⟩ (e.symm (Multiplicative.ofAdd (1 : ℤ)))
  have hone := fundamentalGroup_map_eq_one_of_nullhomotopic i hn ⟨x, hx⟩ a
  have hbad := congrArg (fun z => (e z).toAdd) (ha.symm.trans hone)
  rw [MulEquiv.apply_symm_apply, e.map_one] at hbad
  exact (one_ne_zero : (1 : ℤ) ≠ 0) hbad

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.CarriesFundamentalGroupOnto.not_nullhomotopic_inclusion_in_solid_torus then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.CarriesFundamentalGroupOnto.not_nullhomotopic_inclusion_in_solid_torus"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.CarriesFundamentalGroupOnto.not_nullhomotopic_inclusion_in_solid_torus ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.CarriesFundamentalGroupOnto.not_nullhomotopic_inclusion_in_solid_torus

theorem IsPLHomeomorphInto.not_nullhomotopic_model_longitude_of_carrying_image
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    {P C J : Set (EuclideanSpace ℝ (Fin 3))} {S : Set M}
    {u : EuclideanSpace ℝ (Fin 3) → M} (hu : IsPLHomeomorphInto 3 u P)
    (hC : IsCombinatorialSolidTorus C) (hCP : C ⊆ P) (hJ : J.Nonempty) (hJC : J ⊆ C)
    (hS : IsTopologicalSolidTorus S) (hCS : u '' C ⊆ S)
    (hcarry : CarriesFundamentalGroupOnto (u '' J) S) :
    ¬ (⟨inclusion hJC, continuous_inclusion hJC⟩ : C(J, C)).Nullhomotopic := by
  have huC := (hu.isPLOn.mono_of_isPolyhedron hC.isPolyhedron hCP).isPLHomeomorphInto_model
    hC.isPolyhedron.isCompact (hu.injOn.mono hCP)
  have himage : IsTopologicalSolidTorus (u '' C) :=
    hC.1.image_of_continuousOn_injOn huC.continuousOn huC.injOn
  have hcarry' := hcarry.of_intermediate_solid_torus himage hS (_root_.Set.image_mono hJC) hCS
  have hmodel := huC.carriesFundamentalGroupOnto_of_image_of_subset hC.isPolyhedron.isCompact hJC hcarry'
  exact hmodel.not_nullhomotopic_inclusion_in_solid_torus hJ hC.1 hJC

run_cmd do
  let env ← Lean.getEnv
  if env.contains `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.not_nullhomotopic_model_longitude_of_carrying_image then
    throwError "Refusing to shadow existing declaration DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.not_nullhomotopic_model_longitude_of_carrying_image"
  Lean.modifyEnv fun env => Lean.addAlias env `DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.not_nullhomotopic_model_longitude_of_carrying_image ``Submission.DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphInto.not_nullhomotopic_model_longitude_of_carrying_image

end DifferentialGeometry.Topology.PiecewiseLinear
