import PiQuasi.WaterBalloonLeakage

set_option autoImplicit false

namespace PiQuasi


/-
Strictly positive finite value four.
-/
def pFour : P :=
  .next (.next (.next .one))


theorem pFour_to_uFour :
    pToU pFour = uFour := by
  rfl


/-
Intrinsic residual seam length attached to one
finite traditional-pi stage.

Its value is exactly

4 / oddDenom(next stage).

The numerator is positive by construction.
-/
def piSeamGap
    (s : TraditionalPiPotentialStage) :
    PositiveFraction :=
  {
    num := pFour
    den := oddDenom (.next s.index)
  }


theorem pi_seam_gap_numerator_nonzero
    (s : TraditionalPiPotentialStage) :
    pToU (piSeamGap s).num ≠ U.zero := by
  exact pToU_ne_zero (piSeamGap s).num


/-
Finite exact zero coordinate.
-/
def coordinateZero : Fraction :=
  {
    num := .zero
    den := .one
  }


/-
Finite two-coordinate point.
No continuous completed plane object is required.
-/
structure FinitePoint2 : Type where
  x : Fraction
  y : Fraction


def seamStart :
    FinitePoint2 :=
  {
    x := coordinateZero
    y := coordinateZero
  }


/-
The residual seam is embedded on one finite coordinate
axis.  Its endpoint is separated from the start by the
positive intrinsic gap.
-/
def seamEnd
    (s : TraditionalPiPotentialStage) :
    FinitePoint2 :=
  {
    x :=
      positiveFractionToFraction
        (piSeamGap s)

    y := coordinateZero
  }


/-
The endpoints cannot coincide because equality would
force the strictly positive gap numerator to be zero.
-/
theorem seam_end_ne_start
    (s : TraditionalPiPotentialStage) :
    seamEnd s ≠ seamStart := by

  intro h

  have hx :
      (seamEnd s).x = seamStart.x :=
    congrArg FinitePoint2.x h

  have hn :
      (seamEnd s).x.num =
      seamStart.x.num :=
    congrArg Fraction.num hx

  change
    pToU pFour = U.zero
    at hn

  exact
    pToU_ne_zero pFour hn


def SpatialSeamOpen
    (s : TraditionalPiPotentialStage) :
    Prop :=
  seamEnd s ≠ seamStart


theorem spatial_seam_open_every_finite_stage
    (s : TraditionalPiPotentialStage) :
    SpatialSeamOpen s := by
  exact seam_end_ne_start s


def SpatiallyWaterTight
    (s : TraditionalPiPotentialStage) :
    Prop :=
  seamEnd s = seamStart


def SpatialWaterLeakage
    (s : TraditionalPiPotentialStage) :
    Prop :=
  ¬ SpatiallyWaterTight s


theorem spatial_water_leakage_every_finite_stage
    (s : TraditionalPiPotentialStage) :
    SpatialWaterLeakage s := by
  exact seam_end_ne_start s


theorem spatial_water_leakage_after_refinement
    (s : TraditionalPiPotentialStage) :
    SpatialWaterLeakage
      (refineTraditionalPi s) := by

  exact
    spatial_water_leakage_every_finite_stage
      (refineTraditionalPi s)


/-
Old operational leakage and the new spatial-seam
leakage coincide on every admissible finite stage.
-/
theorem operational_leakage_iff_spatial_leakage
    (s : TraditionalPiPotentialStage) :
    WaterLeakage s ↔ SpatialWaterLeakage s := by

  constructor

  · intro _
    exact
      spatial_water_leakage_every_finite_stage s

  · intro _
    exact
      water_leakage_at_every_finite_stage s


def FiniteSpatialWaterTightWitness : Prop :=
  ∃ s : TraditionalPiPotentialStage,
    SpatiallyWaterTight s


theorem no_finite_spatial_watertight_witness :
    ¬ FiniteSpatialWaterTightWitness := by

  intro h

  cases h with
  | intro s hs =>
      exact seam_end_ne_start s hs


/-
Potential persistence is expressed universally over
every admissible constructed stage, not by introducing
a completed final stage.
-/
def PersistentSpatialLeakage : Prop :=
  (s : TraditionalPiPotentialStage) →
    SpatialWaterLeakage s


theorem persistent_spatial_leakage :
    PersistentSpatialLeakage := by

  intro s

  exact
    spatial_water_leakage_every_finite_stage s


structure SpatialPiWaterBalloon : Type where
  piStage : TraditionalPiPotentialStage


def SpatialBalloonLeaks
    (b : SpatialPiWaterBalloon) :
    Prop :=
  SpatialWaterLeakage b.piStage


def SpatialBalloonWaterTight
    (b : SpatialPiWaterBalloon) :
    Prop :=
  SpatiallyWaterTight b.piStage


theorem every_finite_spatial_pi_balloon_leaks
    (b : SpatialPiWaterBalloon) :
    SpatialBalloonLeaks b := by

  exact
    spatial_water_leakage_every_finite_stage
      b.piStage


def FiniteSpatialNonLeakingBalloonWitness : Prop :=
  ∃ b : SpatialPiWaterBalloon,
    SpatialBalloonWaterTight b


theorem no_finite_spatial_nonleaking_balloon :
    ¬ FiniteSpatialNonLeakingBalloonWitness := by

  intro h

  cases h with
  | intro b hb =>
      exact
        seam_end_ne_start
          b.piStage
          hb


end PiQuasi
