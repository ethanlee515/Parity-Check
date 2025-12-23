#!/usr/bin/env python3

import gen_matrices
from gen_matrices import *

def row_supports(H):
    """
    H: 2D numpy array with entries 0/1
    Returns: list of lists, supports[r] = columns where H[r][c] == 1
    """
    m, n = H.shape
    supports = []
    for r in range(m):
        cols = []
        for c in range(n):
            if H[r, c] == 1:
                cols.append(c)
        supports.append(cols)
    return supports

if __name__ == "__main__":
	x, y = build_xy(6, 6)

	A_terms = [(3,0), (0,1), (0,2)]   # x^3 + y + y^2
	B_terms = [(0,3), (1,0), (2,0)]   # y^3 + x + x^2

	A = eval_poly(x, y, A_terms)
	B = eval_poly(x, y, B_terms)

	HX, HZ = build_HX_HZ(A, B)
	print(row_supports(HZ)[0])
