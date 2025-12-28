#!/usr/bin/env python3

import gen_matrices
from gen_matrices import *
import galois
import json

def xor_chain(vs):
    if not vs:
        return "false"
    term = vs[0]
    for v in vs[1:]:
        term = f"(xor {term} {v})"
    return term

def all_lines(HX, HZ, distance, is_z_error = True):
	(H1, H2) = (HX, HZ) if is_z_error else (HZ, HX)
	lines = []
	lines.append("(set-logic QF_LIA)")
	m, n = H1.shape
	lines = lines + declare_vars(n)
	lines = lines + parity_constraints(H1)
	lines = lines + weight_constraint(n, distance)
	GF = galois.GF(2)
	GF_H = GF(H2)
	N = GF_H.null_space()
	lines = lines + stabilizer_constraints(N)
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
	lines.append(f") {distance - 1}))")
	return lines

def build_mats(l, m, a, b):
	x, y = build_xy(l, m)
	A = eval_poly(x, y, a)
	B = eval_poly(x, y, b)
	return build_HX_HZ(A, B)

def stabilizer_constraints(ker):
	k, n = ker.shape
	lines = ["(assert (or"]
	for i in range(k):
		cols = [j for j in range(n) if int(ker[i, j]) == 1]
		vs = [f"v{j}" for j in cols]
		lines.append(f"\t(= {xor_chain(vs)} true)")
	lines.append("))")
	return lines

if __name__ == "__main__":
	with open("config.json") as f:
		params = json.load(f)
	l = int(params["l"])
	m = int(params["m"])
	A = [tuple(pair) for pair in params["A"]]
	B = [tuple(pair) for pair in params["B"]]
	distance = int(params.get("distance", 6))
	is_z_error = bool(params.get("is_z_error", True))
	HX, HZ = build_mats(l, m, A, B)
	lines = all_lines(HX, HZ, distance, is_z_error)
	for line in lines:
		print(line)
