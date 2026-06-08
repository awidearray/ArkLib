import ArkLib.ToMathlib.CorrelatedAgreementListDecodingClosed
import ArkLib.ProofSystem.Stir.MainThm
import ArkLib.ProofSystem.Whir.RBRSoundness

-- The original keystone (still has the line-1819 sorry, signature unchanged):
#print axioms ProximityGap.correlatedAgreement_affine_curves

-- The new standalone CLOSED keystone (deliverable):
#print axioms ArkLib.CorrelatedAgreementListDecodingClosed.correlatedAgreement_affine_curves_listDecoding_closed

-- The genuine betaRec brick it routes through:
#print axioms ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec

-- stir / whir soundness:
#print axioms StirIOP.stir_rbr_soundness
#print axioms WhirIOP.whir_rbr_soundness
