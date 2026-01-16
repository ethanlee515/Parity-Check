# Parity Check

Hitting some error-correcting codes with cvc5.

## Usage

1. Modify "config.json" as needed
2. Generate SMT inputs by `./write_smt.py > 72-12-6-Z.smt2`
3. Feed the ".smt2" file into an SMT solver

## Requirements

* Python with `numpy`, `scipy`, `galois`, and `json` packages
* Some kind of SMT solver (such as cvc5)

## Theory

Distance is typically defined using linear integer programming.
In order to make use of SMT solvers, we provide a reduction from CSS code distance to Boolean satisfiability.
Let $H_X$ and $H_Z$ be parity-check matrices.
Distance $d_X$ is then defined by the following integer programming problem:

Compute $w(\vec{x})$ subject to the constraints:
* Undetectable: $H_Z \vec{x} = \vec{0}$
* Nontrivial: $\vec{x}\notin \mathsf{rowspace}(H_Z)$

Now, suppose we want to show that the distance is at least $d_X\geq d_0$.
As we want an UNSAT instance, we then have the following constraint:

$$\sum_i \texttt{int}(x_i) < d_0$$

Which is allowed, as SMT solvers understand integers.
The constraint $H_Z \vec{x} = \vec{0}$ then corresponds to the following formula:

$$\forall i, \neg(\oplus_{j: H_{ij}=1} x_j)$$

Which is a direct translation from addition and multiplication modulo 2 to XORs and ANDs.
Finally, the constraint $\vec{x}\notin \mathsf{rowspace}(H_Z)$ is translated as follows:
1. We make use of the fact that $\mathsf{rowspace}(H_Z)=(\mathsf{ker}(H_Z))^\perp$,
   so the constraint is equivalent to $\vec{x}\notin(\mathsf{ker}(H_Z))^\perp$.
2. We decompose the space $\mathsf{ker}(H_Z)=\set{\vec{s}_ {1},\ldots, \vec{s}_\ell}$.
3. We arrive at $\exists i, \vec{x} \cdot \vec{s}_ i \ne 0$. Or equivalently,

$$\wedge_ i ( \oplus_{j \in \vec{s}_ i} x_ {ij} )$$
