import PiQuasi.SpatialSeamLeakage

set_option autoImplicit false

namespace PiQuasi


/- ============================================================
   I. FINITE DELAY ORDER
   ============================================================ -/

/-
Finite order used only for delay comparison.

No actually completed time axis is represented.
-/
def DelayLE : U → U → Prop
  | .zero, _ =>
      True

  | .next _, .zero =>
      False

  | .next a, .next b =>
      DelayLE a b


/-
The successor of any finite delay lies strictly
outside that delay.
-/
theorem delay_successor_not_le_self
    (d : U) :
    ¬ DelayLE (.next d) d := by

  induction d with

  | zero =>
      intro h
      exact h

  | next d ih =>
      change
        ¬ DelayLE (.next d) d

      exact ih


/-
There is no finite delay that contains every
finite delay.

This is potential unboundedness, not an actually
completed infinite time object.
-/
def FiniteDelayCeiling : Prop :=
  ∃ maximum : U,
    ∀ d : U,
      DelayLE d maximum


theorem no_finite_delay_ceiling :
    ¬ FiniteDelayCeiling := by

  intro h

  cases h with
  | intro maximum hmax =>

      have hs :
          DelayLE (.next maximum) maximum :=
        hmax (.next maximum)

      exact
        delay_successor_not_le_self
          maximum
          hs


/- ============================================================
   II. EXACT FINITE OPERATIONAL FLUID TRANSPORT
   ============================================================ -/

/-
A deliberately minimal transport state.

contained d:
  the operational parcel has d finite transport
  steps remaining before escape through an already
  open boundary.

escaped:
  the parcel has crossed the modeled boundary.

This is not Navier--Stokes and is not presented as
a literal physical water theorem.
-/
inductive FluidState : Type where
  | contained : U → FluidState
  | escaped : FluidState


def fluidStep :
    FluidState →
    FluidState

  | .escaped =>
      .escaped

  | .contained .zero =>
      .escaped

  | .contained (.next d) =>
      .contained d


def fluidRun :
    U →
    FluidState →
    FluidState

  | .zero, q =>
      q

  | .next n, q =>
      fluidRun n (fluidStep q)


/-
Any chosen finite transport delay is exhausted
after exactly one further finite step.
-/
theorem fluid_run_next_delay_escapes
    (d : U) :
    fluidRun
      (.next d)
      (.contained d)
      =
      .escaped := by

  induction d with

  | zero =>
      rfl

  | next d ih =>
      change
        fluidRun
          (.next d)
          (.contained d)
        =
        .escaped

      exact ih


/- ============================================================
   III. OPEN-BOUNDARY OPERATIONAL LEAKAGE
   ============================================================ -/

/-
The geometry and the transport dynamics remain separate.

openBoundary is supplied externally.
-/
def OperationalEscapeAt
    (openBoundary : Prop)
    (delay time : U) :
    Prop :=

  openBoundary
  ∧
  fluidRun time (.contained delay) = .escaped


theorem open_boundary_escape_after_any_finite_delay
    (openBoundary : Prop)
    (hOpen : openBoundary)
    (d : U) :
    OperationalEscapeAt
      openBoundary
      d
      (.next d) := by

  constructor

  · exact hOpen

  · exact
      fluid_run_next_delay_escapes d


/-
Potentially unbounded finite-delay leakage:

for every proposed finite delay ceiling m,
there exists a strictly larger finite delay d
for which the operational escape still occurs.

No completed infinity is constructed.
-/
def PotentiallyUnboundedOperationalLeakage
    (openBoundary : Prop) :
    Prop :=

  ∀ maximum : U,
    ∃ d : U,
      ¬ DelayLE d maximum
      ∧
      OperationalEscapeAt
        openBoundary
        d
        (.next d)


theorem open_boundary_potentially_unbounded_operational_leakage
    (openBoundary : Prop)
    (hOpen : openBoundary) :
    PotentiallyUnboundedOperationalLeakage
      openBoundary := by

  intro maximum

  refine
    ⟨.next maximum, ?_, ?_⟩

  · exact
      delay_successor_not_le_self
        maximum

  · exact
      open_boundary_escape_after_any_finite_delay
        openBoundary
        hOpen
        (.next maximum)


/- ============================================================
   IV. INSTANTIATION WITH THE EXISTING OPERATIONAL PI SEAM
   ============================================================ -/

def SpatialPiOpenBoundary
    (s : TraditionalPiPotentialStage) :
    Prop :=
  SpatialSeamOpen s


theorem spatial_pi_boundary_open
    (s : TraditionalPiPotentialStage) :
    SpatialPiOpenBoundary s := by

  exact
    spatial_seam_open_every_finite_stage s


theorem spatial_pi_model_potentially_unbounded_operational_leakage
    (s : TraditionalPiPotentialStage) :
    PotentiallyUnboundedOperationalLeakage
      (SpatialPiOpenBoundary s) := by

  exact
    open_boundary_potentially_unbounded_operational_leakage
      (SpatialPiOpenBoundary s)
      (spatial_pi_boundary_open s)


/- ============================================================
   V. EXPLICIT PHYSICAL INTERPRETATION BRIDGE
   ============================================================ -/

/-
A physical interpretation is NOT silently assumed.

To interpret operational escape as literal physical
fluid leakage, a separate model must prove this bridge.

The bridge can encode scale, parcel size, material
properties, pressure, surface tension, viscosity,
molecular effects, or any other physical assumptions
required by the intended application.
-/
structure FluidInterpretation : Type where

  physicallyLeaksAt :
    TraditionalPiPotentialStage →
    U →
    Prop

  operationalToPhysical :
    (s : TraditionalPiPotentialStage) →
    (d : U) →
    OperationalEscapeAt
      (SpatialPiOpenBoundary s)
      d
      (.next d) →
    physicallyLeaksAt
      s
      (.next d)


def PotentiallyUnboundedPhysicalLeakage
    (F : FluidInterpretation)
    (s : TraditionalPiPotentialStage) :
    Prop :=

  ∀ maximum : U,
    ∃ d : U,
      ¬ DelayLE d maximum
      ∧
      F.physicallyLeaksAt
        s
        (.next d)


/-
Conditional physical result.

The theorem does not manufacture the physical bridge;
it exposes it as an explicit argument.
-/
theorem potentially_unbounded_physical_leakage_under_bridge
    (F : FluidInterpretation)
    (s : TraditionalPiPotentialStage) :
    PotentiallyUnboundedPhysicalLeakage
      F
      s := by

  intro maximum

  refine
    ⟨.next maximum, ?_, ?_⟩

  · exact
      delay_successor_not_le_self
        maximum

  · exact
      F.operationalToPhysical
        s
        (.next maximum)
        (
          open_boundary_escape_after_any_finite_delay
            (SpatialPiOpenBoundary s)
            (spatial_pi_boundary_open s)
            (.next maximum)
        )


end PiQuasi
