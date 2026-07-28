# ROADMAP — moved

This file has moved to [`docs/history/ROADMAP.md`](history/ROADMAP.md).

A stub is kept at the old path because four `.lean` headers cite `docs/ROADMAP.md`
(`Checker/CoverEmit.lean`, `Proofs/Encoding/CoverExtract.lean`,
`Proofs/Encoding/CanonicalInv.lean`, `Proofs/Flow/StratifiedBarrier.lean`). Those files
sit upstream of the whole proof layer, so editing their comments would force a
world rebuild for a path change — see the rebuild-hygiene discipline.

For what is live today, start at [`docs/READING-GUIDE.md`](READING-GUIDE.md).
