# SymGF
[![DOI](https://img.shields.io/badge/DOI-10.1088%2F0953--8984%2F23%2F41%2F415301-blue.svg)](https://doi.org/10.1088/0953-8984/23/41/415301)

## 📌 Cite

This repository implements and extends the **SymGF** symbolic framework introduced in the following paper.

If you use this code in academic work, please cite:

```bibtex
@article{Feng_2011,
  doi = {10.1088/0953-8984/23/41/415301},
  url = {https://doi.org/10.1088/0953-8984/23/41/415301},
  year = {2011},
  month = {sep},
  publisher = {IOP Publishing},
  volume = {23},
  number = {41},
  pages = {415301},
  author = {Feng, Zimin and Sun, Qing-feng and Wan, Langhui and Guo, Hong},
  title = {SymGF: a symbolic tool for quantum transport analysis and its application to a double quantum dot system},
  journal = {Journal of Physics: Condensed Matter},
  abstract = {We report the development and an application of a symbolic tool, called SymGF, for analytical derivations of quantum transport properties using the Keldysh nonequilibrium Green’s function (NEGF) formalism. The inputs to SymGF are the device Hamiltonian in the second quantized form, the commutation relation of the operators and the truncation rules of the correlators. The outputs of SymGF are the desired NEGF that appear in the transport formula, in terms of the unperturbed Green’s function of the device scattering region and its coupling to the device electrodes. For complicated transport analysis involving strong interactions and correlations, SymGF provides significant assistance in analytical derivations. Using this tool, we investigate coherent quantum transport in a double quantum dot system where strong on-site interaction exists in the side-coupled quantum dot. Results obtained by the higher-order approximation and Hartree–Fock approximation are compared. The higher-order approximation reveals Kondo resonance features in the density of states and conductances. Results are compared both qualitatively and quantitatively to the experimental data reported in the literature.}
}
```

---

## 📖 About

**SymGF** is a symbolic Mathematica package for deriving nonequilibrium Green’s functions (NEGF) using the **equation-of-motion (EOM)** method in quantum transport problems.

It is designed for:

* Strongly interacting mesoscopic systems
* Anderson / quantum dot models
* Keldysh NEGF formalism
* Symbolic derivation of Green’s function hierarchies and decoupling schemes

Instead of doing long and error-prone hand derivations, SymGF:

* Takes a Hamiltonian in second-quantized operator form
* Uses operator commutation/anticommutation relations
* Applies user-defined truncation / decoupling rules
* Automatically generates and simplifies the EOM hierarchy

---

## 📂 Repository contents

* `SymGF.m` — Core Mathematica package
* `SymGF Manual-v4.nb` — Manual and documentation notebook
* `FengDefault.nb` — Example / default workflow notebook

---

## 🧰 Requirements

* Wolfram **Mathematica** (any modern version does not work; this code originates from ~2011 and needs major modernization)

---

## 🚀 Quick start

1. Clone your fork:

```bash
git clone https://github.com/<your-username>/SymGF.git
cd SymGF
```

2. Open Mathematica and set the working directory to this folder.

3. Load the package:

```mathematica
Get["SymGF.m"]
```

If needed:

```mathematica
Get[FileNameJoin[{NotebookDirectory[], "SymGF.m"}]]
```

4. Open and evaluate:

* `FengDefault.nb` for a working example
* `SymGF Manual-v4.nb` for documentation and usage patterns

---

## 🧠 Typical workflow

1. Define the Hamiltonian in second-quantized form
2. Define operator algebra (commutators / anticommutators)
3. Define correlator truncation / decoupling rules
4. Generate equation-of-motion chains
5. Solve and simplify symbolic Green’s function relations
6. Export expressions for analytical or numerical evaluation

---

## 🎯 Scope and philosophy

SymGF is focused on:

* Symbolic correctness
* Reproducibility of long EOM derivations
* Assisting human analytical work (not replacing physical modeling decisions)
* Handling complex interacting systems where manual derivation becomes intractable

---

## 🛠️ This fork: goals

This fork aims to:

* Modernize the Mathematica code style
* Add bosonic operators