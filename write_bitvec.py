#!/usr/bin/env python3

import gen_matrices
from gen_matrices import *
import galois
import json
from write_smt import *
from itertools import product
from pathlib import Path
import numpy

def serialize_matrix(M):
  s = 0
  for k in range(M.shape[0] * M.shape[1]):
    i = int(k / M.shape[1])
    j = k % M.shape[1]
    if M[i, j]:
      s += (1 << k)
  return s

def remove_dependent(H):
    GF = galois.GF(2)
    H = GF(H)

    basis = []
    pivot_cols = []
    kept_indices = []
    removed_indices = []

    for i, row in enumerate(H):
        v = row.copy()

        # 既存の basis で reduce
        for b, p in zip(basis, pivot_cols):
            if v[p] != 0:
                v -= v[p] * b   # GF(2) では XOR と同じ

        # zero になったら従属
        if np.all(v == 0):
            removed_indices.append(i)
            continue

        # 新しい pivot
        p = int(np.nonzero(v)[0][0])

        # pivot を 1 に正規化（GF(2) では基本的に不要だが一般形）
        v = v / v[p]

        basis.append(v)
        pivot_cols.append(p)
        kept_indices.append(i)

    new_matrix = H[kept_indices]
    return removed_indices, new_matrix

if __name__ == "__main__":
  with open("configs.json") as f:
    params_set = json.load(f)
  out_dir = Path("outputs")
  out_dir.mkdir(parents=True, exist_ok=True)
  #for (params, is_z_error) in product(params_set, [True, False]):
  params = params_set[3]
  l = int(params["l"])
  m = int(params["m"])
  A = [tuple(pair) for pair in params["A"]]
  B = [tuple(pair) for pair in params["B"]]
  HX, HZ = build_mats(l, m, A, B)
  bad_rows, HX_indep = remove_dependent(HX)
  print(f"bad_rows = {bad_rows}")
  print(f"new shape = {HX_indep.shape}")
  print(f"HX serialized = {hex(serialize_matrix(HX_indep))}")
  #lines = improved_all_lines(HX, HZ, distance, is_z_error)
  #out_path = out_dir / f"{2 * l * m}-{'Z' if is_z_error else "X"}.smt2"
  #with out_path.open("w") as out_file:
  #	for line in lines:
  #		print(line, file=out_file)
  #print(f"HX shape = {HX.shape}")
  #print(f"HX serialized = {hex(serialize_matrix(HX))}")
  #GF = galois.GF(2)
  #GF_H = GF(HX)
  # N = GF_H.null_space()
  # print(f"N shape = {N.shape}")
  # print(f"N serialized = {hex(serialize_matrix(N))}")
  #print(f"Full rank check: {numpy.linalg.matrix_rank(GF_H)}")
  #print(f"HX serialized = {hex(serialize_matrix(GF_H))}")

  #R = GF_H.row_reduce()
  #independent_rows = np.any(R != 0, axis=1)
  #print(independent_rows)
  #newHX = GF_H[independent_rows]

  #print(newHX.shape)