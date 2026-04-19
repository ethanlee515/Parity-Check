#!/usr/bin/env python3

import gen_matrices
from gen_matrices import *
import galois
import json
from write_smt import *
from itertools import product
from pathlib import Path

def serialize_matrix(M):
  s = 0
  for k in range(M.shape[0] * M.shape[1]):
    i = k % M.shape[0]
    j = int(k / M.shape[0])
    if M[i, j]:
      s += (1 << k)
  return s

if __name__ == "__main__":
  with open("configs.json") as f:
    params_set = json.load(f)
  out_dir = Path("outputs")
  out_dir.mkdir(parents=True, exist_ok=True)
  #for (params, is_z_error) in product(params_set, [True, False]):
  params = params_set[0]
  l = int(params["l"])
  m = int(params["m"])
  A = [tuple(pair) for pair in params["A"]]
  B = [tuple(pair) for pair in params["B"]]
  distance = int(params.get("distance", 6))
  HX, HZ = build_mats(l, m, A, B)
  #lines = improved_all_lines(HX, HZ, distance, is_z_error)
  #out_path = out_dir / f"{2 * l * m}-{'Z' if is_z_error else "X"}.smt2"
  #with out_path.open("w") as out_file:
  #	for line in lines:
  #		print(line, file=out_file)
  print(f"HX shape = {HX.shape}")
  print(f"HX serialized = {hex(serialize_matrix(HX))}")
  GF = galois.GF(2)
  GF_H = GF(HZ)
  N = GF_H.null_space()
  print(f"N shape = {N.shape}")
  print(f"N serialized = {hex(serialize_matrix(N))}")
