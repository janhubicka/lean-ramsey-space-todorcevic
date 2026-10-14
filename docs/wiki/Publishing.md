# Publishing the Ramsey-space research wiki

The authoritative source is `docs/wiki/` on `janhubicka/lean-ramsey-space-todorcevic`. The main `docs/wiki/README.md` is the wiki's Home page; other named Markdown files are ordinary wiki pages. The separate GitHub Wiki is at:

https://github.com/janhubicka/lean-ramsey-space-todorcevic/wiki

**Publication verified (14 October 2026).** The Wiki was initialized and [workflow run 38626621204](https://github.com/janhubicka/lean-ramsey-space-todorcevic/actions/runs/38626621204) pushed the full documentation to the separate Wiki `master` branch, commit `7e5bc43`. The [live Wiki](https://github.com/janhubicka/lean-ramsey-space-todorcevic/wiki) is available.

**Important:** putting documentation files in the main repository does *not* itself publish them to the GitHub Wiki tab. GitHub stores the Wiki in a separate `lean-ramsey-space-todorcevic.wiki.git` repository. The publishing workflow is defined in `.github/workflows/publish-wiki.yml`.

## First initialization

If the wiki is still empty, a repository editor must go to the Wiki URL, choose **Create the first page**, set the title to **Home**, and save any placeholder text. This one-time action initializes the separate Git repository. The `gollum` event or a manual workflow run can then sync all source-controlled pages.

Once initialized, the publishing workflow runs on changes to `docs/wiki/**`, on `gollum`, and on explicit `workflow_dispatch`. It checks that the wiki repository exists and then runs `Andrew-Chen-Wang/github-wiki-action@v5` with `path: docs/wiki`, preprocessing, and clone strategy. Its currently installed v5 implementation **does issue `git push -f`** in the successful run, even though the workflow specifies clone strategy. Treat source-controlled Wiki files as authoritative; avoid manual edits in the Wiki repository. It rewrites local Markdown references for Wiki page URLs.

Until a successful wiki-sync run is verified, use the immediately readable source page at [docs/wiki/README.md](README.md) and the linked pages. Do not treat a skipped Wiki job as a successful publication.

## Updating and checking

1. Change the Markdown in `docs/wiki/` through a normal pull request.
2. Verify the Lean kernel and theorem type CI if the change touches code, and review mathematical accuracy for all documentation changes.
3. Merge when reviewed. The workflow updates the GitHub Wiki if initialized.
4. Check the GitHub Actions publish job and the *live* Wiki URL before announcing it as published.

The workflow does not create a missing Wiki repository or alter Lean proof objects. Its v5 action currently force-pushes the Wiki branch; this is documented so independent manual Wiki edits are not mistakenly expected to survive synchronization.
