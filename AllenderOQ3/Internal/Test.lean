/-!
# Obsolete scratch (superseded)

This file previously held a draft of `incidenceCylinder_shiftLayers` that
carried a `sorry` for a motive-rewrite equality
(`ell + 1 + m = ell + m + 1`).  That obligation is now discharged in full
inside `AllenderOQ3.Internal.CylNormal` (`incidenceCylinder_shiftLayers`,
`sorry`-free), which sidesteps the motive issue by indexing the shifted
layers as `m + ell`, so that the successor layer `m + (ell + 1)` is
*definitionally* `(m + ell) + 1`.

The draft here is therefore redundant and has been removed to keep the trust
boundary honest.  See `AllenderOQ3.Internal.CylNormal` for the live
certificate-transport lemmas (`mapCyclicListing`, `mapArcOrderCertificate`,
`cyclic_rotation_map`, `incidenceCylinder_shiftLayers`,
`incidenceCylinder_restrict`, `incidenceCylinder_prunedCircuit`).

This module intentionally declares nothing.
-/
