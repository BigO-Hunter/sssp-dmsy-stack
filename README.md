# sssp-dmsy-stack

Research shelf: durable copy plus axiom-audit seam report of the DMSY near-optimal directed-SSSP stack (stages A0–A4).
Construction: DMSY algorithm (upstream, attributed); durable copy, build harness and axiom audit ours. AI-assisted (darkhipo swarm), disclosed.
Status: A4 full `lake build` green (2028 jobs, exit 0); `sorryAx` confined to exactly two documented source lines (`A4/A4/Main.lean:65/:80`, report §8.1). The top-level statement now carries the paper's `2 ≤ t` regime (`a4_joint` antecedent; see `BaseContain.pullCap_add_fpCap_le_memCap_iff` — the child-size step holds iff `2 ≤ t`), a transcription correction rather than a weakening. A 2026-11-08 closure attempt re-verified the build + audit from a fresh clone and reduced the two seams to one: `theoremT` reduces to `a4_joint`'s `bound` clause, blocked at `LoopBInv` / `ChildLabelFloor` (see the report's §8.1 status section; both named `sorry`s stand). See `SORRY_SEAM_REPORT.md`.

---

## Why this repo is up

Private research shelf (active seam-closing): a durable copy + axiom-audit seam report of the near-optimal DMSY directed-SSSP stack — the audit trail (two named sorries, one reduced) is the intended public good once the seams close.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

Open work: close the remaining sorry seam (`LoopBInv` / `ChildLabelFloor`, report §8.1); fresh-clone rebuild audits.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). The name is unclaimed in software licensing (checked 2026-11-09) and is deliberately not "Copyfree" — the Copyfree Initiative's certification mark — since CFSF's anti-enclosure condition is excluded by their standard.  Vendored third-party material keeps its upstream license — see [NOTICE](NOTICE.md).
