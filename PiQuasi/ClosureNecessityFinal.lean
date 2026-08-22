import PiQuasi.PiQuasiCircleFinal

set_option autoImplicit false

namespace PiQuasi


/-
One finitely executed circle driven by one
finite stage of the traditional pi process.
-/
structure FiniteTraditionalPiCircle : Type where
  piStage : TraditionalPiPotentialStage


/-
Operational geometric closure certificate.

Exact closure requires that no further exact pi
correction remain unresolved at the endpoint.
-/
structure GeometricClosureCertificate
    (c : FiniteTraditionalPiCircle) : Prop where
  piTerminal :
    TraditionalPiTerminal c.piStage


def GeometricallyClosed
    (c : FiniteTraditionalPiCircle) :
    Prop :=
  GeometricClosureCertificate c


/-
Closure necessarily supplies terminality of the
pi process used to determine that endpoint.
-/
theorem closed_circle_implies_pi_terminal
    (c : FiniteTraditionalPiCircle) :
    GeometricallyClosed c →
    TraditionalPiTerminal c.piStage := by
  intro h
  exact h.piTerminal


/-
But no admissible finite traditional-pi stage
is terminal.
-/
theorem finite_pi_circle_not_geometrically_closed
    (c : FiniteTraditionalPiCircle) :
    ¬ GeometricallyClosed c := by

  intro h

  have ht :
      TraditionalPiTerminal c.piStage :=
    closed_circle_implies_pi_terminal c h

  exact
    traditional_pi_stage_ne_terminal
      c.piStage
      ht


def FiniteClosedTraditionalPiCircleWitness : Prop :=
  ∃ c : FiniteTraditionalPiCircle,
    GeometricallyClosed c


theorem no_finite_closed_traditional_pi_circle_witness :
    ¬ FiniteClosedTraditionalPiCircleWitness := by

  intro h

  cases h with
  | intro c hc =>
      exact
        finite_pi_circle_not_geometrically_closed
          c
          hc


/-
A finite water-filled balloon carries one such
finite pi-driven circular membrane.
-/
structure FinitePiWaterBalloon : Type where
  membrane : FiniteTraditionalPiCircle


/-
Water-tight containment requires geometric closure.
-/
structure WaterTightCertificate
    (b : FinitePiWaterBalloon) : Prop where
  closedMembrane :
    GeometricallyClosed b.membrane


def WaterTight
    (b : FinitePiWaterBalloon) :
    Prop :=
  WaterTightCertificate b


def Leaks
    (b : FinitePiWaterBalloon) :
    Prop :=
  ¬ WaterTight b


theorem water_tight_implies_closed_circle
    (b : FinitePiWaterBalloon) :
    WaterTight b →
    GeometricallyClosed b.membrane := by
  intro h
  exact h.closedMembrane


theorem water_tight_implies_pi_terminal
    (b : FinitePiWaterBalloon) :
    WaterTight b →
    TraditionalPiTerminal b.membrane.piStage := by

  intro h

  exact
    closed_circle_implies_pi_terminal
      b.membrane
      (water_tight_implies_closed_circle b h)


theorem every_finite_traditional_pi_balloon_leaks
    (b : FinitePiWaterBalloon) :
    Leaks b := by

  intro h

  have ht :
      TraditionalPiTerminal b.membrane.piStage :=
    water_tight_implies_pi_terminal b h

  exact
    traditional_pi_stage_ne_terminal
      b.membrane.piStage
      ht


def FiniteWaterTightPiBalloonWitness : Prop :=
  ∃ b : FinitePiWaterBalloon,
    WaterTight b


theorem no_finite_watertight_pi_balloon_witness :
    ¬ FiniteWaterTightPiBalloonWitness := by

  intro h

  cases h with
  | intro b hb =>
      exact
        every_finite_traditional_pi_balloon_leaks
          b
          hb


/-
The strongest potential-infinity statement available
without constructing a completed final object:

every admissible finite balloon leaks.
-/
def PersistentPiBalloonLeakage : Prop :=
  (b : FinitePiWaterBalloon) → Leaks b


theorem persistent_pi_balloon_leakage :
    PersistentPiBalloonLeakage := by
  intro b
  exact every_finite_traditional_pi_balloon_leaks b


end PiQuasi
