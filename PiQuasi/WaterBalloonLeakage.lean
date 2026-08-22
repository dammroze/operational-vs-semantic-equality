import PiQuasi.PiQuasiCircleFinal

set_option autoImplicit false

namespace PiQuasi


/-
The unresolved correction attached to the next
finite refinement of the traditional pi process.

This is the operational seal defect.
-/
def piSealDefect
    (s : TraditionalPiPotentialStage) :
    ExactSignedFraction :=
  gregoryPiTerm (.next s.index)


/-
Exact zero seal defect.
-/
def SealDefectZero
    (s : TraditionalPiPotentialStage) :
    Prop :=
  CorrectionZero (piSealDefect s)


/-
A membrane is operationally sealed only when
its pi-driven closure defect is exactly zero.
-/
def MembraneSealed
    (s : TraditionalPiPotentialStage) :
    Prop :=
  SealDefectZero s


/-
Leakage means failure of exact sealing.
-/
def WaterLeakage
    (s : TraditionalPiPotentialStage) :
    Prop :=
  ¬ MembraneSealed s


/-
The seal defect is nonzero at every admissible
finite stage.
-/
theorem pi_seal_defect_nonzero
    (s : TraditionalPiPotentialStage) :
    ¬ SealDefectZero s := by

  exact
    gregory_pi_term_nonzero
      (.next s.index)


theorem membrane_never_sealed_at_finite_stage
    (s : TraditionalPiPotentialStage) :
    ¬ MembraneSealed s := by

  exact
    pi_seal_defect_nonzero s


theorem water_leakage_at_every_finite_stage
    (s : TraditionalPiPotentialStage) :
    WaterLeakage s := by

  exact
    membrane_never_sealed_at_finite_stage s


/-
The theorem is stable under one additional
finite refinement.
-/
theorem water_leakage_after_refinement
    (s : TraditionalPiPotentialStage) :
    WaterLeakage (refineTraditionalPi s) := by

  exact
    water_leakage_at_every_finite_stage
      (refineTraditionalPi s)


/-
No finitely constructed stage can provide
a water-tight seal witness.
-/
def FiniteWaterTightWitness : Prop :=
  ∃ s : TraditionalPiPotentialStage,
    MembraneSealed s


theorem no_finite_water_tight_witness :
    ¬ FiniteWaterTightWitness := by

  intro h

  cases h with
  | intro s hs =>
      exact
        membrane_never_sealed_at_finite_stage
          s
          hs


/-
"Along the potential infinity" is expressed without
constructing an actual-infinite terminal object:

for an arbitrary admissible finite stage, leakage holds.
-/
def PersistentPotentialLeakage : Prop :=
  (s : TraditionalPiPotentialStage) →
    WaterLeakage s


theorem persistent_potential_leakage :
    PersistentPotentialLeakage := by

  intro s

  exact
    water_leakage_at_every_finite_stage s


/-
Abstract water-filled balloon driven by one finite
traditional-pi construction state.
-/
structure PiWaterBalloon : Type where
  piStage : TraditionalPiPotentialStage


def BalloonWaterTight
    (b : PiWaterBalloon) :
    Prop :=
  MembraneSealed b.piStage


def BalloonLeaks
    (b : PiWaterBalloon) :
    Prop :=
  WaterLeakage b.piStage


theorem every_finite_pi_water_balloon_leaks
    (b : PiWaterBalloon) :
    BalloonLeaks b := by

  exact
    water_leakage_at_every_finite_stage
      b.piStage


def FiniteNonLeakingPiBalloonWitness : Prop :=
  ∃ b : PiWaterBalloon,
    BalloonWaterTight b


theorem no_finite_nonleaking_pi_balloon :
    ¬ FiniteNonLeakingPiBalloonWitness := by

  intro h

  cases h with
  | intro b hb =>
      exact
        membrane_never_sealed_at_finite_stage
          b.piStage
          hb


end PiQuasi
