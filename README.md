# LLM-Assisted Proof Construction for Parameterized Hardware Design

Select a model and one of six transformation tasks, then follow the live Rocq
goals, hypotheses, accepted commands and diagnostics in your terminal:
`preHorners`, `Horners`, `monitor`, `contour_row`, `contour_right`, and `Cu0_Cu1`.

[TUTORIAL.md](TUTORIAL.md) introduces Ruby and states the six examples.
The `library/` directory contains circuit definitions and supporting proofs;
[library/tutorial.v](library/tutorial.v) provides small executable examples.

## Setup

Use Python 3.12, Coq 8.19.2 and coq-lsp 0.2.3+8.19. With opam and its system
build prerequisites installed on Linux:

```sh
python3.12 -m venv .venv
. .venv/bin/activate
pip install -r requirements.txt
opam switch create proof-tool ocaml-base-compiler.4.14.2
eval "$(opam env --switch=proof-tool --set-switch)"
opam repository add coq-released https://coq.inria.fr/opam/released
opam install coq.8.19.2 coq-lsp.0.2.3+8.19
```

Keep `coqc`, `coqchk` and `coq-lsp` on PATH in the terminal used for the prover.
`requirements.txt` pins the Python dependencies, including the CoqPyt revision.

## Inspect and prepare offline

Run commands from the repository root:

```sh
python scripts/run_prover.py --list
python scripts/run_prover.py --model gpt-6.1-sol --benchmark Cu0_Cu1 --prepare
```

Preparation checks the input hashes, compiles the selected dependencies, runs
`coqchk`, and writes the task's prompts under ignored `runs/`. It requires no
provider credentials and makes no model requests.

To compile the executable tutorial examples:

```sh
for module in axioms rel basic wire wire_rec loop rec rows tutorial; do
    coqc -Q library '' "library/$module.v" || break
done
coqchk -Q library '' -silent tutorial
```

## Models and settings

[environment/models.json](environment/models.json) provides twelve presets for
the models the paper evaluates, with provider and model IDs,
reasoning controls and output limits. The interactive menu uses these presets.

[environment/SETTINGS.md](environment/SETTINGS.md) lists the model presets,
construction limits, conversation handling and evaluation measures.

## Interactive prover

```sh
python scripts/run_prover.py
```

Choose a model and a task from the menus. Set the selected provider's
`OPENAI_API_KEY`, `ANTHROPIC_API_KEY`, or `GEMINI_API_KEY` environment variable,
or enter the key at the hidden terminal prompt. `GOOGLE_API_KEY` also works.
The runner excludes credentials from its logs.

For a session with an explicit request cap:

```sh
python scripts/run_prover.py --model gpt-6.1-sol --benchmark preHorners --max-calls 64
```

Horner requires your own checked `preHorners` result. Pass the `candidate.v`
from a successful local run:

```sh
python scripts/run_prover.py --model gpt-6.1-sol --benchmark Horners \
    --prerequisite runs/YOUR_PREHORNERS_SESSION/candidate.v --max-calls 64
```

The runner checks that prerequisite before making a model request.

Use `--max-output`, `--effort`, `--plan-rounds`, and `--timeout` to adjust a
session; Anthropic also supports `--thinking`. Use `--model ID --provider PROVIDER`
for an unlisted model, or `--models-file` for another registry. `--help` lists all options.
Providers bill usage to your account; the recorded model IDs depend on your
provider's availability and access.

Each session saves its current proof state, checked prefix, exchanges and verdict
under `runs/`. `--output PATH` selects a new directory. Ctrl-C stops the session
and preserves its latest recorded state. `--verbose` also prints prompts and
responses. Acceptance requires the unchanged statement and permitted actions,
closed obligations, compilation, the two extensionality assumptions and
independent `coqchk` checking.

## Task inputs

Each `benchmarks/<name>/` directory contains the target, supplied mathematical
derivation, library interface and representation notes. The manifest selects
the exact library modules for each task and records input hashes. Model inputs
include definitions and checked lemma statements; they exclude supporting proof
bodies and tactic implementations.

The repository omits reference and generated formal proof scripts for the six
benchmark targets. `.gitignore` excludes `runs/`, compiled artifacts and common
credential files.
