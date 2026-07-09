import RelCertifier.Oracle
import RelCertifier.Smt
open RelCertifier
-- pure core: standard three only
#print axioms flow_cert_sound
#print axioms tderiv_correct
#print axioms lieDeriv_correct
-- IO boundary: standard three + z3_unsat_sound (single trusted leaf)
#print axioms flow_certified
-- emitter faithfulness (pure)
#print axioms ilieDeriv_toHost
#print axioms iflowQuery_toHost
