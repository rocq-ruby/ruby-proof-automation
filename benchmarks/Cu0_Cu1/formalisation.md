# Representation of the convolver transformation

Cu0 and Cu1 are parameterised by the explicit delay family D and the natural window size. The target assumes both cancellation directions for D nat and uses the supplied definitions of Cu0, Cu1, CuCell1 and mac.

For the local pointwise loader equivalence, take input (x,ws) and skewed taps prs. The left side has an existential pair prs0,xo with row_pw n (fork; SND pi1) (x,ws) (prs0,xo) and tri n (FST E) prs0 prs. The right side has an existential xo with row_pw n (fork; SND (pi1; E)) (x,ws) (prs,xo). Use snoc_inv, row_pw_snoc, tri_snoc and pow_fst. dist_cell_pt and dist_cellD_pt characterise the two cells; dist_row_thread identifies the undelayed row output, chainD_pow the delayed output, and pow_func equates powered witnesses. For pair equality use projections with f_equal or destruct equalities. cancel_total and cancel_func derive the needed pointwise properties from the two premises. Use row_dual and expand the series/projection witnesses to package the loader equality. The generic row_rdl_below then applies with the delayed distributor, mac, and junk value 0 of type nat. The pointwise loader equivalence and structural loader theorem are local obligations.

The library modules are axioms, rel, basic, wire, wire_rec, rec, rows, twod
and convolver_support in `library/`. The loader equivalences and target solution
are absent from the supplied library.
