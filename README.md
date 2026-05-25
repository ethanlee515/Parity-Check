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
* Nontrivial: $\vec{x}\notin \mathsf{rowspace}(H_X)$

Now, suppose we want to show that the distance is at least $d_X\geq d_0$.
As we want an UNSAT instance, we then have the following constraint:

$$\sum_i \texttt{int}(x_i) < d_0$$

Which is allowed, as SMT solvers understand integers.
The constraint $H_Z \vec{x} = \vec{0}$ then corresponds to the following formula:

$$\forall i, \neg(\oplus_{j: H_{ij}=1} x_j)$$

Which is a direct translation from addition and multiplication modulo 2 to XORs and ANDs.
Finally, as $\mathsf{rowspace}(H_X)$ is a very large set,
the constraint $\vec{x}\notin \mathsf{rowspace}(H_X)$ cannot be translated directly.
It is treated as follows:
1. We make use of the fact that $\mathsf{rowspace}(H_X)=(\mathsf{ker}(H_X))^\perp$,
   so the constraint is equivalent to $\vec{x}\notin(\mathsf{ker}(H_X))^\perp$.
2. We unfold the $\perp$ operator and arrive at $\exists \vec{y}\in\mathsf{ker}(H_X), \vec{x}\cdot\vec{y}\ne 0$.
3. We choose a basis $\mathsf{ker}(H_X)=\mathsf{span}\set{\vec{s}_1,\ldots, \vec{s}_\ell}$.
4. Since the dot product is linear, $\vec{x}\cdot\vec{y}=1$ for some kernel vector iff
   $\vec{x}\cdot\vec{s}_i\ne 0$ for some basis vector. Or equivalently,

$$\vee_i \left( \oplus_{j : (s_i)_j = 1} x_j \right)$$
