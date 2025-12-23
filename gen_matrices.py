#!/usr/bin/env python3

'''
Generates the parity-check matrices
Mostly written by ChatGPT
'''

import numpy as np
from scipy.sparse import csr_matrix, eye, kron, hstack, vstack

def shift_matrix(n: int) -> csr_matrix:
    """
    Cyclic shift S_n: e_i -> e_{i+1 mod n}.
    """
    rows = np.arange(n, dtype=int)
    cols = (rows + 1) % n
    data = np.ones(n, dtype=np.int8)
    return csr_matrix((data, (rows, cols)), shape=(n, n))

def gf2_add(*mats: csr_matrix) -> csr_matrix:
    """
    Sum of matrices mod 2. Works by adding in integers then reducing mod 2.
    """
    out = mats[0].copy()
    for M in mats[1:]:
        out = out + M
    out.data %= 2
    out.eliminate_zeros()
    return out

def gf2_mul(A: csr_matrix, B: csr_matrix) -> csr_matrix:
    """
    Matrix multiply over GF(2): (A @ B) mod 2.
    """
    C = (A @ B).tocsr()
    C.data %= 2
    C.eliminate_zeros()
    return C

def gf2_pow(A: csr_matrix, k: int) -> csr_matrix:
    """
    Fast exponentiation over GF(2).
    """
    n, m = A.shape
    assert n == m
    result = eye(n, format="csr", dtype=np.int8)
    base = A
    e = k
    while e > 0:
        if e & 1:
            result = gf2_mul(result, base)
        e >>= 1
        if e:
            base = gf2_mul(base, base)
    return result

def build_xy(l: int, m: int):
    Sl = shift_matrix(l)
    Sm = shift_matrix(m)
    Il = eye(l, format="csr", dtype=np.int8)
    Im = eye(m, format="csr", dtype=np.int8)

    x = kron(Sl, Im, format="csr")
    y = kron(Il, Sm, format="csr")
    return x, y

def eval_poly(x: csr_matrix, y: csr_matrix, terms):
    """
    terms: list of (ax, ay) meaning x^ax y^ay
    """
    parts = []
    for ax, ay in terms:
        part = gf2_mul(gf2_pow(x, ax), gf2_pow(y, ay))
        parts.append(part)
    return gf2_add(*parts)

def build_HX_HZ(A: csr_matrix, B: csr_matrix):
	HX = hstack([A, B], format="csr")
	HZ = hstack([B.transpose().tocsr(),
	A.transpose().tocsr()], format="csr")
	HX_dense = HX.toarray().astype(int)
	HZ_dense = HZ.toarray().astype(int)
	return HX_dense, HZ_dense

if __name__ == "__main__":
	x, y = build_xy(6, 6)

	A_terms = [(3,0), (0,1), (0,2)]   # x^3 + y + y^2
	B_terms = [(0,3), (1,0), (2,0)]   # y^3 + x + x^2

	A = eval_poly(x, y, A_terms)
	B = eval_poly(x, y, B_terms)

	HX, HZ = build_HX_HZ(A, B)

