# Trace Logic in Rocq

This repo is an attempt at formalizing *Trace Logic*,
which was defined in the paper [Verifying Relational Properties using Trace Logic](https://arxiv.org/abs/1906.09899),
and then further refined in the paper [Trace Logic for Inductive Loop Reasoning](https://arxiv.org/abs/2008.01387).

Citations:
```
@misc{barthe2019verifyingrelationalpropertiesusing,
      title={Verifying Relational Properties using Trace Logic}, 
      author={Gilles Barthe and Renate Eilers and Pamina Georgiou and Bernhard Gleiss and Laura Kovacs and Matteo Maffei},
      year={2019},
      eprint={1906.09899},
      archivePrefix={arXiv},
      primaryClass={cs.LO},
      url={https://arxiv.org/abs/1906.09899}, 
}
@misc{georgiou2020tracelogicinductiveloop,
      title={Trace Logic for Inductive Loop Reasoning}, 
      author={Pamina Georgiou and Bernhard Gleiss and Laura Kovács},
      year={2020},
      eprint={2008.01387},
      archivePrefix={arXiv},
      primaryClass={cs.LO},
      url={https://arxiv.org/abs/2008.01387}, 
}
```


## Build Instructions

1. Download Rocq (formerly known as Coq) from https://rocq-prover.org/install

2. To be able to follow along proofs, you must choose a compatible editor
from the available options in the Rocq installation page,
and follow the setup instructions there.
For the most common option, VSCode:

	a. Download VSCode from https://code.visualstudio.com/

	b. Install the VsCoq language server (instructions at https://rocq-prover.org/)

	c. Install the VsCoq extension for VSCode by searching for "VsCoq" inside VSCode's extensions view (https://marketplace.visualstudio.com/items?itemName=maximedenes.vscoq)

3. Run `./build.sh` (or `./build.ps1` on Windows) from the root of this repo

	If you're using Rocq on Windows without WSL
	and you haven't enabled running PowerShell scripts,
	you can instead run `coqc -Q src Project ./src/<file>.v` on every file in `./src/`.

4. Open a file in `./src/` and start stepping through it to follow along proofs.

	In VSCode this is done using the down arrow button that appears on the top-right when you open a Rocq file.

This project should work with all Rocq versions (since the rename),
but it was built and tested with Rocq version `8.20.1`.
