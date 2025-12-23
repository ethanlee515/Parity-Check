#!/usr/bin/env python3

import gen_matrices
from gen_matrices import *

def xor_chain(vs):
    if not vs:
        return "false"
    term = vs[0]
    for v in vs[1:]:
        term = f"(xor {term} {v})"
    return term

def all_lines(H, distance):
	lines = []
	lines.append("(set-logic QF_UFLIA)")
	m, n = H.shape
	lines = lines + declare_vars(n)
	lines = lines + parity_constraints(H)
	lines = lines + weight_constraint(n, distance)
	lines.append("(check-sat)")
	return lines

def declare_vars(n):
	lines = []
	for j in range(n):
		lines.append(f"(declare-const v{j} Bool)")
	return lines

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

def parity_constraints(H):
	lines = []
	supports = row_supports(H)
	for r, cols in enumerate(supports):
		vs = [f"v{j}" for j in cols]
		lines.append(f"(assert (= {xor_chain(vs)} false))")
	return lines

def weight_constraint(n, distance):
	lines = []
	lines.append("(assert (<= (+")
	for j in range(n):
		lines.append(f"\t(ite v{j} 1 0)")
	lines.append(f") {distance}))")
	return lines

def build_mats(l, m, a, b):
	x, y = build_xy(l, m)
	A = eval_poly(x, y, a)
	B = eval_poly(x, y, b)
	return build_HX_HZ(A, B)



if __name__ == "__main__":
	HX, HZ = build_mats(6, 6, [(3,0), (0,1), (0,2)], [(0,3), (1,0), (2,0)])
	lines = all_lines(HZ, 6)
	for line in lines:
		print(line)

