# Handoff with Muse

This repo is also worked on by Muse (Gavriel's personal assistant).
The two agents communicate through `HANDOFF.md` at the repo root, with git
as the transport.

At the start of every session on this repo:
1. Pull the latest changes.
2. Read `HANDOFF.md` (protocol + log) before doing anything else.

At the end of every session:
1. Append a dated entry to `HANDOFF.md`: what changed (files + commit),
   what's next, and any open questions for Muse.
2. Commit and push, so Muse sees it.

Rules: append only, never edit or delete Muse's entries. Work, decisions,
and questions only — no chat, no secrets, no keys or tokens.
