# Ruby circuit definitions and transformations

This tutorial introduces Ruby circuit relations, their calculation laws, and the six tasks in the transformation suite.
The six tasks are `preHorners`, `Horners`, `monitor`, `contour_row`, `contour_right`, and `Cu0_Cu1`.
All dimensions are natural numbers, including zero, and each equation requires compatible port types.
Rocq names accompany the mathematical notation. Each task has a proof interface listing its definitions, available lemma statements, and structural operations.

## Ruby basics

### Circuit relations and wiring

Ruby describes hardware through component relations and their connections [1, 2].
Write $`R:A\sim B`$ for a circuit relation and $`R(a,b)`$ for consistency of its port values; in Rocq, `rel A B := A -> B -> Prop`.
Products group ports, as in $`\mathrm{ADDER}(\langle u,v\rangle,w)\iff w=u+v`$.
A length-$`n`$ vector has type $`\mathbf A_n`$ (`t A n`) and values $`\langle a_0,\ldots,a_{n-1}\rangle`$, with $`\langle\rangle`$ the empty vector.
Products and vectors are distinct types; nested brackets record port grouping.
Relations need not be total or single-valued.
Clocked blocks can relate streams: a register has $`D(a,b)\iff\forall t\in\mathbb Z.\;b_t=a_{t-1}`$.
The transformation parameters below range over arbitrary relations satisfying their stated premises.

Series, parallel, identity and converse satisfy

```math
\begin{aligned}
(R;S)(a,c)&\iff\exists b.\;R(a,b)\land S(b,c),\\
[R,S](\langle a,c\rangle,\langle b,d\rangle)&\iff R(a,b)\land S(c,d),\\
I_A(a,b)&\iff a=b,\\
R^{-1}(b,a)&\iff R(a,b).
\end{aligned}
```

Series composition hides a shared signal; converse exchanges the two interfaces and does not itself justify cancellation.
Projection, swap, duplication and regrouping wires are

```math
\begin{aligned}
\pi_1(\langle a,b\rangle,c)&\iff c=a, \\
\pi_2(\langle a,b\rangle,c)&\iff c=b, \\
\mathrm{swp}(\langle a,b\rangle,y)&\iff y=\langle b,a\rangle,\\
\mathrm{fork}(a,y)&\iff y=\langle a,a\rangle,\\
\mathrm{lsh}(\langle\langle a,b\rangle,c\rangle,y)
 &\iff y=\langle a,\langle b,c\rangle\rangle,\\
\mathrm{rsh}(\langle a,\langle b,c\rangle\rangle,y)
 &\iff y=\langle\langle a,b\rangle,c\rangle.
\end{aligned}
```

The Rocq names are `pi1`, `pi2`, `swp`, `fork`, `lsh` and `rsh`.
For $`R:A\sim B`$, write $`\mathrm{fst}R=[R,I_C]`$ and $`\mathrm{snd}R=[I_C,R]`$ (`FST`, `SND`); the untouched port has type $`C`$.
Feedback for $`R:(X\times S)\sim(S\times Y)`$ is $`(\mathrm{loop}R)(x,y)\iff\exists s.\;R(\langle x,s\rangle,\langle s,y\rangle)`$.
A delay in the feedback path supplies clocked state; the six tasks use the relational algebra directly.

Equality means agreement on all external port values.
Functional and propositional extensionality turn pointwise equivalence into Rocq equality, enabling rewriting [3, 4].
Principal calculation laws include

```math
\begin{aligned}
(R;S);T&=R;(S;T), & I;R&=R=R;I,\\
[P;Q,R;S]&=[P,R];[Q,S], & [I_A,I_B]&=I_{A\times B},\\
(R;S)^{-1}&=S^{-1};R^{-1}, & (R^{-1})^{-1}&=R,\\
[R,S]^{-1}&=[R^{-1},S^{-1}], & I_A^{-1}&=I_A.
\end{aligned}
```

The regrouping wires cancel in both orders, and $`\mathrm{swp};\mathrm{swp}=I`$, with appropriately reversed port types.
Reassociation changes expression brackets; regrouping wires change the grouping of port values.
Single-valuedness (`det R`) means $`\forall a,b,c.\;R(a,b)\land R(a,c)\Rightarrow b=c`$, without requiring an output for every input.
Series, parallel and powers preserve single-valuedness; for single-valued $`T`$, $`T;\mathrm{fork}=\mathrm{fork};[T,T]`$.

### Vectors, powers and recursive combinators

Write $`a::\mathbf v`$ for prepending, $`\mathbf v\mathbin{\Vert}\langle a\rangle`$ for appending and $`\mathbf v\mathbin{\Vert}\mathbf w`$ for concatenation.
The corresponding wires and splitter are

```math
\begin{aligned}
\mathrm{apl}_n(\langle a,\mathbf v\rangle,\mathbf w)
 &\iff\mathbf w=a::\mathbf v,\\
\mathrm{apr}_n(\langle\mathbf v,a\rangle,\mathbf w)
 &\iff\mathbf w=\mathbf v\mathbin{\Vert}\langle a\rangle,\\
\mathrm{apn}_{p,q}(\langle\mathbf v,\mathbf w\rangle,\mathbf u)
 &\iff\mathbf u=\mathbf v\mathbin{\Vert}\mathbf w,\\
F_n(a,\mathbf v)&\iff\mathbf v=\langle a,\ldots,a\rangle\in\mathbf A_n.
\end{aligned}
```

Their Rocq names are `apl n`, `apr n`, `apn p q` and `mfork n`.
Each append/prepend wire and its converse cancel in both orders; $`F_0`$ relates every input to the unique empty vector.
For $`E:A\sim A`$, define $`E^0=I_A`$, $`E^{n+1}=E^n;E`$ and $`E^{-n}=(E^{-1})^n`$.
Then $`E^m;E^n=E^{m+n}`$ and $`(E^n)^{-1}=(E^{-1})^n`$, without cancellation assumptions.
Identity, converse and power use `id A`, `R^~1` and `R ^^ n` in Rocq.

Map (`mapn n R`) repeats $`R:A\sim B`$ independently across lanes; triangle (`tri n E`) places $`E^i`$ on lane $`i`$:

```math
\begin{aligned}
(\mathrm{map}_nR)(\mathbf a,\mathbf b)&\iff\forall i\lt n.\;R(a_i,b_i),\\
(\triangle_nE)(\mathbf a,\mathbf b)&\iff\forall i\lt n.\;E^i(a_i,b_i),\\
\mathrm{map}_0R&=\varepsilon_{A,B},\\
\triangle_0E&=I_{\mathbf A_0},\\
\mathrm{map}_{n+1}R
 &=\mathrm{apr}_n^{-1};[\mathrm{map}_nR,R];\mathrm{apr}_n,\\
\triangle_{n+1}E
 &=\mathrm{apr}_n^{-1};[\triangle_nE,E^n];\mathrm{apr}_n.
\end{aligned}
```

Here $`\varepsilon_{A,B}:\mathbf A_0\sim\mathbf B_0`$ relates the empty vectors; map's append wires use the respective element types.
Map preserves series, identity and converse, and $`(\triangle_nE)^{-1}=\triangle_n(E^{-1})`$.
The commuting law is $`\mathrm{map}_nE;\triangle_nE=\triangle_nE;\mathrm{map}_nE`$.

Right reduction uses $`R:(A\times B)\sim B`$; left reduction uses $`S:(B\times A)\sim B`$.
Their interfaces are $`(\mathbf A_n\times B)\sim B`$ and $`(B\times\mathbf A_n)\sim B`$, respectively:

```math
\begin{aligned}
(\mathrm{rdr}_0R)(\langle\langle\rangle,b\rangle,c)&\iff b=c,\\
\mathrm{rdr}_{n+1}R
 &=\mathrm{fst}(\mathrm{apr}_n^{-1});\mathrm{lsh};
   \mathrm{snd}R;\mathrm{rdr}_nR,\\
(\mathrm{rdl}_0S)(\langle b,\langle\rangle\rangle,c)&\iff b=c,\\
\mathrm{rdl}_{n+1}S
 &=\mathrm{snd}(\mathrm{apl}_n^{-1});\mathrm{rsh};
   \mathrm{fst}S;\mathrm{rdl}_nS.
\end{aligned}
```

Thus right reduction processes the last element first and left reduction the first.
Both reductions preserve the scalar accumulator when the vector is empty.
The Rocq names are `rdr n R` and `rdl n S`.

### Cells, rows and grids

A four-way cell has domain ports on its left and top and range ports on its bottom and right.
Beside joins horizontal boundaries; below joins vertical boundaries.
Each of the following equations has its own compatible port types:

```math
\begin{aligned}
&(R\leftrightarrow S)(\langle a,\langle b,c\rangle\rangle,
                      \langle\langle d,e\rangle,f\rangle) \iff\exists g.\;R(\langle a,b\rangle,\langle d,g\rangle)
                    \land S(\langle g,c\rangle,\langle e,f\rangle),\\
&(R\updownarrow S)(\langle\langle a,b\rangle,c\rangle,
                    \langle d,\langle e,f\rangle\rangle) \iff\exists g.\;R(\langle a,g\rangle,\langle d,e\rangle)
                    \land S(\langle b,c\rangle,\langle g,f\rangle).
\end{aligned}
```

These are `R <--> S` and `R <||> S` in Rocq; the existential quantifier hides the internal boundary signal.

Rows repeat $`R:(A\times B)\sim(C\times A)`$ horizontally, with interface $`(A\times\mathbf B_n)\sim(\mathbf C_n\times A)`$.
Columns repeat $`S:(A\times B)\sim(B\times C)`$ vertically, with interface $`(\mathbf A_n\times B)\sim(B\times\mathbf C_n)`$:

```math
\begin{aligned}
(\mathrm{row}_0R)(\langle a,\langle\rangle\rangle,
                       \langle\langle\rangle,a'\rangle)&\iff a=a',\\
\mathrm{row}_{n+1}R
 &=\mathrm{snd}(\mathrm{apl}_n^{-1});
   (R\leftrightarrow\mathrm{row}_nR);\mathrm{fst}(\mathrm{apl}_n),\\
(\mathrm{col}_0S)(\langle\langle\rangle,b\rangle,
                       \langle b',\langle\rangle\rangle)&\iff b=b',\\
\mathrm{col}_{n+1}S
 &=\mathrm{fst}(\mathrm{apl}_n^{-1});
   (S\updownarrow\mathrm{col}_nS);\mathrm{snd}(\mathrm{apl}_n).
\end{aligned}
```

An empty row or column preserves the scalar boundary while changing its position in the interface.
For $`R:(A\times B)\sim(B\times A)`$, a grid is a row of $`m`$ columns containing $`n`$ cells each:

```math
\mathrm{grid}_{m,n}R=\mathrm{row}_m(\mathrm{col}_nR)
 : (\mathbf A_n\times\mathbf B_m)\sim(\mathbf B_m\times\mathbf A_n).
```

The names `row n R`, `col n R` and `grid m n R` follow this boundary order.

## Transformation examples

### 1. Power commutation: `preHorners`

**Purpose.** Extend a single-stage commutation law to any natural number of stages.

**Definitions.** Let $`P:A\sim A`$, $`Q:B\sim B`$ and $`R:(A\times B)\sim B`$.
Both sides of the transformation have type $`(A\times B)\sim B`$.

**Premises and target.** Assume

```math
[P,Q];R=R;Q.
```

For every natural $`n`$, the target is

```math
[P^n,Q^n];R=R;Q^n.
```

### 2. Horner transformation: `Horners`

**Purpose.** Move powers on the vector inputs and accumulator into a reduction with the same combined stage at every position.

**Definitions.** Let $`P:A\sim A`$, $`Q:B\sim B`$ and $`R:(A\times B)\sim B`$.
The triangle $`\triangle_nP`$ applies increasing powers of $`P`$ across the vector, and $`\mathrm{rdr}_nR`$ reduces the vector with an accumulator of type $`B`$.
Both sides of the transformation have type $`(\mathbf A_n\times B)\sim B`$.

**Premises and target.** Assume

```math
[P,Q];R=R;Q.
```

For every natural $`n`$, the target is

```math
[\triangle_nP,Q^n];\mathrm{rdr}_nR
=\mathrm{rdr}_n(\mathrm{snd}Q;R).
```

**Prerequisites.** The Horner transformation uses a checked `preHorners` result from the preceding example.

### 3. Monitor: `monitor`

**Purpose.** Replace a splitter, triangular delay arrangement and reduction over $`2^n`$ values with a recursive circuit.

**Definitions.** Let $`D:A\sim A`$ and $`R:(A\times A)\sim A`$.
The monitor circuits $`P_n`$ and $`Q_n`$ have type $`A\sim A`$.
For $`h:m=n`$, $`\mathrm{cast}_h:\mathbf A_m\sim\mathbf A_n`$ (`cast_rel h`) is equality transport: it preserves vector contents while changing their length index.
It cancels with transport along the reversed equality and satisfies $`\triangle_mD;\mathrm{cast}_h=\mathrm{cast}_h;\triangle_nD`$ and $`F_m;\mathrm{cast}_h=F_n`$.
Let $`\kappa_n`$ transport from length $`2^n`$ to $`1+(2^n-1)`$, equal for every natural $`n`$.
Define

```math
\begin{aligned}
P_n&=F_{2^n};\triangle_{2^n}D;\kappa_n;
      \mathrm{apl}_{2^n-1}^{-1};\mathrm{rdl}_{2^n-1}R,\\
Q_0&=I_A,\\
Q_{n+1}&=Q_n;\mathrm{fork};\mathrm{snd}(D^{2^n});R,\\
T_m&=F_{m+1};\triangle_{m+1}D;
      \mathrm{apl}_m^{-1};\mathrm{rdl}_mR.
\end{aligned}
```

**Premises and target.** Assume

```math
\begin{aligned}
D^{-1};D&=I_A, & [D,D];R&=R;D,\\
\mathrm{rsh};\mathrm{fst}R;R&=\mathrm{snd}R;R,
 &R&\text{ is single-valued}.
\end{aligned}
```

For every natural $`n`$, the target is

```math
P_n=Q_n.
```

These four premises define the monitor task; totality and the opposite cancellation direction are not additional hypotheses.

**Prerequisites.** The supplied checked bridge `P_as_PP` establishes $`P_n=T_{2^n-1}`$, where $`T_m`$ is `PP m`; it preserves $`P_n`$'s cast.
Under the premises above, the library supplies single-valuedness of the structural circuits and $`T_0=I_A`$.

### 4. Row contour: `contour_row`

**Purpose.** Add a relation to each cell's horizontal output and compensate at the row boundaries.

**Definitions.** Let $`R:(A\times B)\sim(B\times A)`$, $`E_A:A\sim A`$ and $`E_B:B\sim B`$.
The row has type $`(A\times\mathbf B_n)\sim(\mathbf B_n\times A)`$.
Paired conjugation abbreviates $`R\mathbin{\backslash\backslash}[S,T]=[T^{-1},S^{-1}];R;[S,T]`$, for $`S:B\sim B`$ and $`T:A\sim A`$.

**Premises and target.** Assume

```math
\begin{aligned}
R&=[E_A,E_B];R;[E_B^{-1},E_A^{-1}],\\
E_A;E_A^{-1}&=I_A,\qquad E_A^{-1};E_A=I_A.
\end{aligned}
```

In Rocq, the cell premise uses paired conjugation: `R = R \\ [EB^~1, EA^~1]`.
The cancellation premises concern $`E_A`$ only.
For every natural $`n`$, the target is

```math
\begin{aligned}
\mathrm{row}_nR
 &=\mathrm{snd}(\triangle_nE_B);
   \mathrm{row}_n(R;\mathrm{snd}E_A);
   [(\triangle_nE_B)^{-1},E_A^{-n}].
\end{aligned}
```

### 5. Right-grid contour: `contour_right`

**Purpose.** Add a relation to each cell's horizontal output and compensate at the grid boundaries.

**Definitions.** Let $`R:(A\times B)\sim(B\times A)`$, $`E_A:A\sim A`$ and $`E_B:B\sim B`$.
The grid $`\mathrm{grid}_{m,n}R`$ contains $`m`$ columns of $`n`$ cells and has type $`(\mathbf A_n\times\mathbf B_m)\sim(\mathbf B_m\times\mathbf A_n)`$.

**Premises and target.** Assume

```math
\begin{aligned}
R&=[E_A,E_B];R;[E_B^{-1},E_A^{-1}],\\
E_A;E_A^{-1}&=I_A,\qquad E_A^{-1};E_A=I_A,\\
E_B;E_B^{-1}&=I_B,\qquad E_B^{-1};E_B=I_B.
\end{aligned}
```

The cell premise uses the paired conjugation notation from the row-contour example.
For every natural $`m`$ and $`n`$, the target is

```math
\begin{aligned}
\mathrm{grid}_{m,n}R
 &=\mathrm{snd}(\triangle_mE_B);
   \mathrm{grid}_{m,n}(R;\mathrm{snd}E_A);
   [(\triangle_mE_B)^{-1},\mathrm{map}_n(E_A^{-m})].
\end{aligned}
```

**Prerequisites.** The supplied outer-grid law `grid_conjugation` states, under the same premises,

```math
\begin{aligned}
\mathrm{grid}_{m,n}R
 &=[\mathrm{map}_nE_A,\mathrm{map}_mE_B];
    \mathrm{grid}_{m,n}R;
    [(\mathrm{map}_mE_B)^{-1},(\mathrm{map}_nE_A)^{-1}].
\end{aligned}
```

This law applies uniform relations at the outer boundaries.
The target additionally inserts a relation into every cell and introduces triangular boundary factors.
The direct grid task establishes the remaining steps without a supplied solution to `contour_row`.

### 6. Convolver regularization: `Cu0_Cu1`

**Purpose.** The convolver transformation replaces a distributor followed by a triangular delay arrangement and a reduction with a row of identical cells.
The reference circuit, `Cu0`, forms pairs of delayed data values and weights before a reduction multiplies and accumulates them.
The regular circuit, `Cu1`, combines data distribution, delay, and multiplication with accumulation in each cell.

**Definitions.** Let $`N=\mathbb N`$ be the value type and write $`\mathbf N_n`$ for the type of weight vectors of length $`n`$.
Rocq uses `nat` for $`N`$.
Both circuits have type $`((N\times N)\times\mathbf N_n)\sim N`$: the first input pair contains the accumulator $`a`$ and data value $`x`$, followed by the weight vector.
The formal task supplies a family `D : forall A : Type, rel A A`; write $`D_N`$ for its instance `D nat`.

The multiply-accumulate relation $`\mathrm{MAC}:(N\times(N\times N))\sim N`$ (`mac` in Rocq) satisfies

```math
\mathrm{MAC}(\langle a,\langle x,w\rangle\rangle,b)
\iff b=a+xw.
```

Let $`P=N\times N`$ be the tap type, holding a data value and its weight.
Define the tap delay $`E=[D_N,I_N]:P\sim P`$ and the distributor cells

```math
\begin{aligned}
R_{\mathrm{dist}}&=\mathrm{fork};\mathrm{snd}\pi_1
   :(N\times N)\sim(P\times N),\\
R_{\mathrm{delay}}&=\mathrm{fork};\mathrm{snd}(\pi_1;D_N)
   :(N\times N)\sim(P\times N).
\end{aligned}
```

The plain cell $`R_{\mathrm{dist}}`$ maps $`\langle x,w\rangle`$ to $`\langle\langle x,w\rangle,x\rangle`$.
The delayed cell $`R_{\mathrm{delay}}`$ has the same tap output and relates its horizontal output $`x'`$ to $`x`$ through $`D_N(x,x')`$.
The distributor $`\mathrm{dstl}_n=\mathrm{row}_n R_{\mathrm{dist}};\pi_1`$ keeps the vector of tap pairs and discards the final horizontal output.
The triangle $`\triangle_n E`$ then applies $`D_N^i`$ to the data on lane $`i`$ while preserving its weight.
The reference circuit is

```math
\mathrm{Cu0}_n
=\mathrm{lsh};
 \mathrm{snd}(\mathrm{dstl}_n;\triangle_n E);
 \mathrm{rdl}_n\mathrm{MAC}.
```

The regular cell places the multiply-accumulate operation above the delayed distributor:

```math
\begin{aligned}
\mathrm{CuCell1}
  &=(\mathrm{MAC};\pi_2^{-1})\updownarrow R_{\mathrm{delay}},\\
\mathrm{Cu1}_n
  &=\mathrm{row}_n\mathrm{CuCell1};\pi_2;\pi_1.
\end{aligned}
```

Here $`\pi_2^{-1}:N\sim(N\times N)`$ pairs the accumulator result with an arbitrary auxiliary value on the bottom port.
The cell therefore has type $`((N\times N)\times N)\sim(N\times(N\times N))`$.
A row carries the accumulator and data value together along its horizontal boundary.
The final $`\pi_2;\pi_1`$ discards the auxiliary vector and data output, keeping the accumulator.
The Rocq definitions are `mac`, `CuCell1`, `Cu0`, and `Cu1`.

**Premises and target.** For every family $`D`$ and every natural $`n`$, the target `Cu0_Cu1` states

```math
\bigl(D_N;D_N^{-1}=I_N\;\land\;D_N^{-1};D_N=I_N\bigr)
\;\Longrightarrow\;
\mathrm{Cu0}_n=\mathrm{Cu1}_n.
```

These are the two cancellation premises on `D nat` in the formal statement.

## References

1. Geraint Jones and Mary Sheeran. “Circuit Design in Ruby.” In Jørgen Staunstrup, editor, *Formal Methods for VLSI Design*, pages 13-70. North-Holland, 1990.
2. Geraint Jones and Mary Sheeran. “Designing Arithmetic Circuits by Refinement in Ruby.” *Science of Computer Programming*, 22(1-2):107-135, 1994. [DOI](https://doi.org/10.1016/0167-6423(94)90009-4).
3. The Coq Development Team. [The Coq Proof Assistant, version 8.19.2](https://rocq-prover.org/releases/8.19.2), 2024.
4. Yves Bertot and Pierre Castéran. *Interactive Theorem Proving and Program Development: Coq'Art: The Calculus of Inductive Constructions*. Springer, 2004. [DOI](https://doi.org/10.1007/978-3-662-07964-5).
