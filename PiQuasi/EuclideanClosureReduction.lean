import PiQuasi.IndependentFiniteProgressBridge

set_option autoImplicit false

namespace PiQuasi


/- ============================================================
   I. EXACT FINITE EUCLIDEAN POINTS
   ============================================================ -/

structure FiniteEuclideanPoint : Type where
  x : ExactSignedFraction
  y : ExactSignedFraction


/-
Coordinate equality is semantic exact-fraction
equality, not structural representation equality.
-/
def EuclideanPointEq
    (a b : FiniteEuclideanPoint) :
    Prop :=
  ExactEq a.x b.x ∧
  ExactEq a.y b.y


def euclideanExactSub
    (a b : ExactSignedFraction) :
    ExactSignedFraction :=
  exactAdd a (exactNeg b)


def euclideanExactSquare
    (a : ExactSignedFraction) :
    ExactSignedFraction :=
  exactMul a a


def euclideanSquaredDistance
    (a b : FiniteEuclideanPoint) :
    ExactSignedFraction :=

  exactAdd
    (euclideanExactSquare
      (euclideanExactSub a.x b.x))
    (euclideanExactSquare
      (euclideanExactSub a.y b.y))


/- ============================================================
   II. GENUINE CIRCLE LAW INTERFACE
   ============================================================ -/

/-
A finite Euclidean circle geometry must provide:

* one fixed center,
* one fixed exact squared radius,
* start and finish endpoints,
* exact proof that both endpoints lie on that same circle.

No terminality predicate occurs here.
No arithmetic residual is inserted as a coordinate
by this interface.
-/
structure FiniteEuclideanCircleGeometry : Type where

  center :
    FiniteEuclideanPoint

  radiusSquared :
    ExactSignedFraction

  start :
    TraditionalPiPotentialStage →
    FiniteEuclideanPoint

  finish :
    TraditionalPiPotentialStage →
    FiniteEuclideanPoint

  startOnCircle :
    (s : TraditionalPiPotentialStage) →
    ExactEq
      (euclideanSquaredDistance
        (start s)
        center)
      radiusSquared

  finishOnCircle :
    (s : TraditionalPiPotentialStage) →
    ExactEq
      (euclideanSquaredDistance
        (finish s)
        center)
      radiusSquared


def EuclideanEndpointClosed
    (G : FiniteEuclideanCircleGeometry)
    (s : TraditionalPiPotentialStage) :
    Prop :=

  EuclideanPointEq
    (G.finish s)
    (G.start s)


/- ============================================================
   III. THE SINGLE REMAINING GEOMETRIC BRIDGE
   ============================================================ -/

/-
This is deliberately separated.

A genuine geometric construction must prove that
equality of its independently constructed Euclidean
endpoints forces stagnation of the exact finite
traditional-pi progress geometry.

TraditionalPiTerminal is NOT assumed here.

The downstream progress-to-terminal implication is
already a derived theorem.
-/
structure EuclideanToFiniteProgressBridge
    (G : FiniteEuclideanCircleGeometry) :
    Prop where

  closureForcesFiniteProgressClosure :
    (s : TraditionalPiPotentialStage) →

    EuclideanEndpointClosed G s →

    EndpointClosed
      TraditionalPiFiniteProgressGeometry
      s


/- ============================================================
   IV. COMPOSITION WITH THE DERIVED FINITE-PROGRESS BRIDGE
   ============================================================ -/

theorem euclidean_closure_forces_pi_terminal
    (G : FiniteEuclideanCircleGeometry)
    (B : EuclideanToFiniteProgressBridge G)
    (s : TraditionalPiPotentialStage) :

    EuclideanEndpointClosed G s →

    TraditionalPiTerminal s := by

  intro hClosed

  have hProgress :
      EndpointClosed
        TraditionalPiFiniteProgressGeometry
        s :=

    B.closureForcesFiniteProgressClosure
      s
      hClosed

  exact
    traditional_pi_progress_closure_forces_terminal
      s
      hProgress


theorem euclidean_endpoint_closure_impossible
    (G : FiniteEuclideanCircleGeometry)
    (B : EuclideanToFiniteProgressBridge G)
    (s : TraditionalPiPotentialStage) :

    ¬ EuclideanEndpointClosed G s := by

  intro hClosed

  have hTerminal :
      TraditionalPiTerminal s :=

    euclidean_closure_forces_pi_terminal
      G
      B
      s
      hClosed

  exact
    traditional_pi_stage_ne_terminal
      s
      hTerminal


def FiniteEuclideanClosureWitness
    (G : FiniteEuclideanCircleGeometry) :
    Prop :=

  ∃ s : TraditionalPiPotentialStage,
    EuclideanEndpointClosed G s


theorem no_finite_euclidean_closure_witness
    (G : FiniteEuclideanCircleGeometry)
    (B : EuclideanToFiniteProgressBridge G) :

    ¬ FiniteEuclideanClosureWitness G := by

  intro h

  cases h with
  | intro s hs =>

      exact
        euclidean_endpoint_closure_impossible
          G
          B
          s
          hs


/- ============================================================
   V. EXACT REDUCTION OF THE REMAINING RESEARCH OBLIGATION
   ============================================================ -/

structure EuclideanClosureReductionResult : Prop where

  finiteProgressBridgeAlreadyDerived :
    (s : TraditionalPiPotentialStage) →
    EndpointClosed
      TraditionalPiFiniteProgressGeometry
      s →
    TraditionalPiTerminal s

  euclideanClosureNeedsOnlyGeometryToProgressBridge :
    (G : FiniteEuclideanCircleGeometry) →
    EuclideanToFiniteProgressBridge G →
    (s : TraditionalPiPotentialStage) →
    EuclideanEndpointClosed G s →
    TraditionalPiTerminal s

  euclideanNonclosureOnceBridgeProvided :
    (G : FiniteEuclideanCircleGeometry) →
    EuclideanToFiniteProgressBridge G →
    (s : TraditionalPiPotentialStage) →
    ¬ EuclideanEndpointClosed G s


theorem euclidean_closure_reduction_result :
    EuclideanClosureReductionResult := by

  exact
    {
      finiteProgressBridgeAlreadyDerived :=
        traditional_pi_progress_closure_forces_terminal

      euclideanClosureNeedsOnlyGeometryToProgressBridge := by
        intro G B s h
        exact
          euclidean_closure_forces_pi_terminal
            G B s h

      euclideanNonclosureOnceBridgeProvided := by
        intro G B s
        exact
          euclidean_endpoint_closure_impossible
            G B s
    }


end PiQuasi
