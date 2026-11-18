Cu0 to Cu1 by a distributor contour and row–reduction fusion

Goal. For every window size n, prove that the reference convolver Cu0 and the regular convolver Cu1 are the same relation. Use both supplied cancellations for the scalar delay d, in both orders. Here d is D at nat. A semicolon composes relations from left to right. A bracketed pair of relations acts in parallel. A negative power denotes the corresponding positive power of the converse relation.

1. Expose the two circuits and type the distributor.

Let W be the weight type nat and let P be the pair type nat × W. Let e = [d, id_W] on P. The plain distributor r = fork ; snd(pi1) has input type nat × W and output type P × nat. It copies the pair to its tap and sends the scalar data on horizontally. Let s = r ; snd(d) = fork ; snd(pi1 ; d). The reference circuit is the input reassociation lsh followed by the loader on the second component and the left reduction by mac. The loader is dstl_n ; triangle_n(e), where dstl_n = row_n(r) ; pi1. The regular circuit is the row of stacked cells (mac ; converse(pi2)) above s, followed by pi2 and then pi1. Those projections keep the final accumulator.

2. Establish the cell wiring law.

Prove [d, id_W] ; r = r ; [e, d]. The left side delays the scalar data before the fork. The right side uses the same delay on both outgoing copies. In the reverse direction, the two delay outputs agree by single-valuedness. Derive this property from the cancellation of converse(d) ; d. One can use relational equality locally on the fork and projections. Prove the powered law [d^i, id_W] ; r = r ; [e^i, d^i] by induction on i, using parallel composition and associativity.

3. Insert the contour and cancel the seams.

For each position i, express the plain cell as

    r = [d^i, id_W] ; s ; [e^(-i), d^(-(i+1))].

To justify the equality, expand s, move the input power across r by the powered wiring law, and cancel on the two output lanes. On the pair lane cancel e^i against e^(-i). On the horizontal lane combine d^i with the extra d in s and cancel against d^(-(i+1)). The law for e follows componentwise from the law for d.

Prove the following row invariant by appending the last cell.

    row_n(r) = row_n(s) ; [triangle_n(converse(e)), d^(-n)].

At zero there are empty vectors and an identity horizontal wire. At the successor, the first n cells give the invariant above. The added plain cell has index n. Its input horizontal d^n follows the prefix output d^(-n), so the seam is identity by cancellation in the reverse order. The weight input carries identity. The remaining output relation on the pair vector appends e^(-n) to the old triangle, using the last-element recursion of the triangle. The last horizontal output is d^(-(n+1)). This closes the induction. Treat the beside seam and the reassociation of the last vector entry separately. The input and output vertical lane types are different, so a row law requiring the same vertical type on both sides cannot be instantiated directly.

4. Project the last horizontal output and cancel the original skew.

Let T = triangle_n(e) and U = triangle_n(converse(e)). The preceding invariant gives

    dstl_n ; T
      = row_n(r) ; pi1 ; T
      = row_n(s) ; [U, d^(-n)] ; pi1 ; T
      = row_n(s) ; pi1 ; U ; T
      = row_n(s) ; pi1.

To move the projection across the parallel relation, show that the discarded horizontal relation d^(-n) is total. The diagonal of converse(d) ; d supplies a predecessor for each scalar, and induction gives totality of every converse power. A discarded lane still needs an output witness in a relational composition. For U ; T, use the last-element recursion of both triangles. Their prefix composition is identity by induction, and their last component cancels e^(-n) against e^n. The empty triangle is identity on the empty vector.

5. Fuse the delayed distributor and the reduction.

Substitute the projected-row equality into the loader position of Cu0, keeping the input reassociation and the reduction in place. The generic row–reduction fusion law changes

    lsh ; snd(row_n(s) ; pi1) ; rdl_n(mac)

into

    row_n((mac ; converse(pi2)) stacked above s) ; pi2 ; pi1.

The cell in this row is exactly CuCell1, so the result is Cu1. The row invariant, the projected loader equality, and the fusion step are the main intermediate obligations. Local pointwise arguments may establish wiring equalities. Use the circuit equalities to transform Cu0 through to Cu1.
