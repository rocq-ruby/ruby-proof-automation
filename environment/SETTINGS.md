# Model and construction settings

## Model presets

[models.json](models.json) supplies the following runner defaults for the twelve
models in the paper.

| Model ID | Reasoning or thinking | Maximum output tokens per request |
| --- | --- | ---: |
| `gpt-6-astra` | medium | 128000 |
| `gpt-6.1-sol` | medium | 128000 |
| `gpt-6-luna` | medium | 128000 |
| `gpt-5.6-sol` | medium | 128000 |
| `gpt-5.4-2026-03-05` | medium | 128000 |
| `o3-2025-04-16` | medium | 100000 |
| `gpt-4.1-2025-04-14` | no reasoning parameter | 32768 |
| `claude-sonnet-5-5` | adaptive, medium effort | 128000 |
| `claude-opus-4-5-20251101` | manual, 10000-token thinking budget, medium effort | 64000 |
| `gemini-3.1-pro-preview` | HIGH | 65536 |
| `gemini-3.8-flash` | HIGH | 65536 |
| `gemini-4-argon` | HIGH | 65536 |

Output limits include reasoning tokens according to each provider's accounting.
Use `--max-output` to lower the limit and `--effort` to adjust reasoning.

## Construction limits and conversations

| Control | Runner default |
| --- | --- |
| Whole-proof attempts | 2 |
| Planning trials | 2; `--plan-rounds` adjusts this |
| Batch attempts per checkpoint | 3 |
| Incremental rounds per checkpoint | 8 |
| Request timeout | 600 seconds; `--timeout` adjusts this |
| Global request cap | No additional cap; `--max-calls N` sets one |

The guided evaluation uses the same 2/2/3/8 construction limits.

Whole-proof attempts start separate conversations. Within a planning trial, the
controller retains accepted commands, model replies and verifier feedback.
A new planning trial resets the proof state and conversation.
OpenAI uses text history; Anthropic and Google retain native response content,
including reasoning signatures. Follow-up requests include the current proof
obligations and diagnostics.

## Task inputs

Each task in `benchmarks/` supplies `target.v`, `paper_proof.md`,
`library_interface.v` and `formalisation.md`.
The manifest records its library dependencies and input hashes. Model inputs
contain definitions and checked lemma statements, excluding proof bodies and
tactic implementations.

The evaluation supplies checked prerequisites independently of model outcomes.
For Horner, the runner requires a checked `preHorners` proof from the user's own
run, supplied through `--prerequisite`.

## Evaluation measures

The guided evaluation comprises twelve models, six tasks and three independent
trials for each model and task: 216 runs.

- **S/W/C:** accepted runs in total, during the whole-proof phase, and through
  checkpoint continuation. Acceptance requires the fixed statement and action
  policy, successful compilation, the declared foundational assumptions and
  independent `coqchk` checking.
- **L/A:** median final proof commands among accepted runs, and median command
  attempts across all three trials. Attempts include rejected commands and
  abandoned scripts; compound tactics and library macros each count once.
- **Requests, tokens and cost:** totals include failed attempts, planning and
  repair. The cost figure uses lower estimates from provider token usage and
  evaluation-time tariffs, excluding two Gemini 3.1 Pro requests with missing usage.

For a local session, `session.json` records effective settings,
`progress.jsonl` records command attempts, `api_*.json` records provider
requests and responses, and `result.json` records the validation outcome.

## Software

The checked environment uses Python 3.12.12, Coq 8.19.2, OCaml 4.14.2 and
coq-lsp 0.2.3+8.19. [requirements.txt](../requirements.txt) pins CoqPyt and the
provider SDKs. See the [README](../README.md#setup) for installation.
