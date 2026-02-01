#!/usr/bin/env python3

import gen_matrices
from gen_matrices import *
import galois
import json
from write_smt import *
from itertools import product
from pathlib import Path

def mem_chain(x, vs):
	assert(vs)
	term = f"(= {vs[0]} {x})"
	for v in vs[1:]:
		term = f"(or {term} (= {v} {x}))"
	return term

def improved_declare_vars(distance, n):
	lines = []
	for j in range(distance - 1):
		lines.append(f"(declare-const loc{j} Int)")
		lines.append(f"(assert (and (<= 0 loc{j}) (< loc{j} {n})))")
	# symmetry breaking...
	for j in range(distance - 2):
		lines.append(f"(assert (<= loc{j} loc{j + 1}))")
	for j in range(n):
		locs = [f"loc{j}" for j in range(distance - 1)]
		vj_val = mem_chain(j, locs)
		lines.append(f"(define-fun v{j} () Bool {vj_val})")
	return lines

def improved_all_lines(HX, HZ, distance, is_z_error = True):
	(H1, H2) = (HX, HZ) if is_z_error else (HZ, HX)
	lines = []
	lines.append("(set-logic QF_LIA)")
	m, n = H1.shape
	lines = lines + improved_declare_vars(distance, n)
	lines = lines + parity_constraints(H1)
	GF = galois.GF(2)
	GF_H = GF(H2)
	N = GF_H.null_space()
	lines = lines + stabilizer_constraints(N)
	lines.append("(check-sat)")
	return lines

if __name__ == "__main__":
	with open("configs.json") as f:
		params_set = json.load(f)
	out_dir = Path("outputs")
	out_dir.mkdir(parents=True, exist_ok=True)
	for (params, is_z_error) in product(params_set, [True, False]):
		l = int(params["l"])
		m = int(params["m"])
		A = [tuple(pair) for pair in params["A"]]
		B = [tuple(pair) for pair in params["B"]]
		distance = int(params.get("distance", 6))
		HX, HZ = build_mats(l, m, A, B)
		lines = improved_all_lines(HX, HZ, distance, is_z_error)
		out_path = out_dir / f"{2 * l * m}-{"Z" if is_z_error else "X"}.smt2"
		with out_path.open("w") as out_file:
			for line in lines:
				print(line, file=out_file)
