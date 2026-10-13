/-  Audit.lean — run with `lake env lean Calib/Audit.lean`; the driver accepts
    only propext, Classical.choice, Quot.sound in the output. -/
import Calib.Obligations

#print axioms Calib.Obligations.perm.exists
#print axioms Calib.Obligations.sort.unambiguous
#print axioms Calib.Obligations.sort.wf
#print axioms Calib.Obligations.sort.impl_correct
#print axioms Calib.Obligations.sort.exists
#print axioms Calib.Obligations.max.unambiguous
#print axioms Calib.Obligations.max.ens_0
#print axioms Calib.Obligations.max.impl_correct
#print axioms Calib.Obligations.max.exists
