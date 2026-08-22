import PiQuasi.AdversarialClassificationFinal

set_option autoImplicit false

namespace PiQuasi


/- ============================================================
   I. NATIVE FINITE EXACT-CLOSURE CERTIFICATE
   ============================================================ -/

/-
A native finite exact-closure certificate contains
one finitely attained stage whose independently
defined endpoints are exactly equal.

No repair, tolerance, epsilon, approximation, or
completed infinite object occurs in this definition.
-/
def NativeFiniteExactClosureCertificate
    (G : FiniteEndpointGeometry) :
    Prop :=
  FiniteEndpointClosureWitness G


theorem no_native_finite_exact_closure_certificate_under_bridge
    (G : FiniteEndpointGeometry)
    (B : PiTerminalClosureBridge G) :
    ¬ NativeFiniteExactClosureCertificate G := by

  exact
    no_finite_endpoint_closure_witness_under_bridge
      G
      B


/- ============================================================
   II. EXTERNAL CORRECTION
   ============================================================ -/

/-
A successful closure certificate may be classified
as originating either from:

1. native finite endpoint closure, or
2. an explicitly external correction.

The correction is deliberately abstract here.
No physical solder, geometry, magnitude, or material
is silently inserted into the theorem.
-/
structure ExactClosureCertification
    (G : FiniteEndpointGeometry) : Type where

  certified : Prop

  externalCorrectionUsed : Prop

  certificationOrigin :
    certified →
      NativeFiniteExactClosureCertificate G
      ∨
      externalCorrectionUsed


/-
If native finite closure is impossible under the
independently proved bridge, then every successful
certificate in this certification model necessarily
uses the external-correction branch.
-/
theorem exact_closure_certification_requires_external_correction
    (G : FiniteEndpointGeometry)
    (B : PiTerminalClosureBridge G)
    (C : ExactClosureCertification G) :
    C.certified →
    C.externalCorrectionUsed := by

  intro hCertified

  cases C.certificationOrigin hCertified with

  | inl hNative =>
      exact
        False.elim
          (
            no_native_finite_exact_closure_certificate_under_bridge
              G
              B
              hNative
          )

  | inr hExternal =>
      exact hExternal


/- ============================================================
   III. NATIVE SUFFICIENCY
   ============================================================ -/

/-
The finite process is called natively sufficient for
exact closure only if it supplies a native finite
endpoint-closure witness.
-/
def NativeFiniteProcessSufficientForExactClosure
    (G : FiniteEndpointGeometry) :
    Prop :=
  NativeFiniteExactClosureCertificate G


theorem finite_process_not_natively_sufficient_under_bridge
    (G : FiniteEndpointGeometry)
    (B : PiTerminalClosureBridge G) :
    ¬ NativeFiniteProcessSufficientForExactClosure G := by

  exact
    no_native_finite_exact_closure_certificate_under_bridge
      G
      B


/- ============================================================
   IV. SAFETY-CRITICAL CERTIFICATION
   ============================================================ -/

/-
Safety-critical admissibility is deliberately abstract.

The only policy encoded here is:

if the system is admissible, an exact closure
certificate must have been issued.
-/
structure SafetyCriticalClosureCertification
    (G : FiniteEndpointGeometry) : Type where

  closureCertificate :
    ExactClosureCertification G

  admissible : Prop

  admissibleRequiresExactClosure :
    admissible →
    closureCertificate.certified


/-
Under an independently established geometric bridge,
any admissible system in this certification model must
therefore use the external-correction branch.
-/
theorem safety_critical_admission_requires_external_correction
    (G : FiniteEndpointGeometry)
    (B : PiTerminalClosureBridge G)
    (S : SafetyCriticalClosureCertification G) :
    S.admissible →
    S.closureCertificate.externalCorrectionUsed := by

  intro hAdmissible

  have hCertified :
      S.closureCertificate.certified :=
    S.admissibleRequiresExactClosure hAdmissible

  exact
    exact_closure_certification_requires_external_correction
      G
      B
      S.closureCertificate
      hCertified


/- ============================================================
   V. FINAL SEPARATION
   ============================================================ -/

structure FiniteClosureCertificationSeparation
    (G : FiniteEndpointGeometry)
    (B : PiTerminalClosureBridge G) : Prop where

  nativeExactClosureUnavailable :
    ¬ NativeFiniteExactClosureCertificate G

  successfulCertificateRequiresExternalCorrection :
    (C : ExactClosureCertification G) →
    C.certified →
    C.externalCorrectionUsed


theorem finite_closure_certification_separation
    (G : FiniteEndpointGeometry)
    (B : PiTerminalClosureBridge G) :
    FiniteClosureCertificationSeparation G B := by

  exact
    {
      nativeExactClosureUnavailable :=
        no_native_finite_exact_closure_certificate_under_bridge
          G
          B

      successfulCertificateRequiresExternalCorrection := by
        intro C hC
        exact
          exact_closure_certification_requires_external_correction
            G
            B
            C
            hC
    }


end PiQuasi
