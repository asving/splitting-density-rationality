# The companion site and how it is rebuilt

The companion site is the folder `claude/splitting-type-density/` of the site repository
`asving/asving.github.io`. It shows the paper with a Lean panel beside each statement, a page about the
formalization, and every Lean file as a highlighted page.

The original generator of the site, `site/build.py`, and the markdown source of the paper,
`PAPER_v2_narrative.md`, were lost in November 2026 with the workspace that held them. The scripts in
this directory are a reconstruction of the generator's page logic, made from its output. They are
validated against the last output of the original: from the Lean sources of tag `v1.1.0` they
reproduce the site folder of 2026-10-17 byte for byte (`test_identity.sh`).

## What the site is built from

This repository at a commit, and the site folder itself. Nothing else.

Hand-written, in the site folder. `refresh.py` never changes these:

- `index.html`: the text of the paper, and which map entries each Lean panel lists.
- `formalization.html`: the prose, the coverage table of section 5, and which statements are shown.
- `lean/index.html` and `lean/decls.html` outside their main block and table body.
- `certificates/`: copies of logs and certificates.
- `data/curation.json`: the hand-curated map from the paper's statements to Lean declarations.
- `data/config.json`: settings. `refresh.py` reads `lean_dirs`, `lean_root_files`, `lean_artifact_url`,
  `prove2me`, `paper` and `prove2me_nodes`.
- `data/prove2me_nodes.json`: a snapshot of the public Prove2Me tree `TypeDensity`.
- `assets/`, `vendor/`, `data/screenshots/`, and the footer of the pages except its last line.

Derived. `refresh.py` rewrites these:

| part | from |
|---|---|
| `lean/**/*.lean` and the root files in `lean/` | the sources at the commit |
| `lean/**/*.html` | the sources, the map (paper chips), `lean_page_template.html`, the footer of `lean/index.html` |
| main block of `lean/index.html` | the sources: file tables, counts, the toolchain line, links to the main theorems and to the corollaries added in v1.2 |
| table body of `lean/decls.html` | the sources, the map, the Prove2Me links |
| Lean panels of `index.html` | the curation, the sources, the Prove2Me links |
| statement blocks of `formalization.html` | the sources. Each `<div class="main-thm">` names its theorem |
| map table of `formalization.html` | the map |
| axiom log of `formalization.html` | `logs/release_axioms.log` of the clone, if the release check was run there |
| `data/paper_lean_map.json` | the curation, the sources, the Prove2Me links, `data/config.json` |
| last line of the footer of every page | the commit and the toolchain |
| record `refresh` in `data/validation.json` | a check of all internal links |
| `lean_commit` in `data/config.json` | the commit |

Carried over. These came from inputs that no longer exist, so `refresh.py` copies them from the site
folder as it finds them:

- From the paper source: label, title, anchor and paper line of the numbered statements, and the list
  `displays`, in `data/paper_lean_map.json`. Also the paper position of each row of the map table.
- From the Prove2Me catalog of the original workspace: which nodes belong to which declaration. This
  is the Prove2Me column of `lean/decls.html`. A declaration without a row gets the node of the same
  name if it is a public theorem. Node labels, names and page ids come from `data/prove2me_nodes.json`.

## Running it

    python3 -I site/refresh.py REPO SITE_DIR

`REPO` is a clone of this repository. `SITE_DIR` is `claude/splitting-type-density` in a clone of the
site repository. The sources are read from `HEAD` of `REPO` with `git archive`, so uncommitted changes
are ignored. Only files whose content changes are written, and a second run changes nothing. Review
the result with `git diff` in the site repository and commit there. Scripts cannot live in the site
repository: its `.gitignore` excludes `*.py`.

For a release, run `tools/release_check_local.sh` and commit first, then refresh. The footer names the
commit, and the axiom log is the one the release check wrote.

To change the map, edit `data/curation.json` in the site folder and refresh. To show another statement
on the formalization page, copy a `<div class="main-thm">` block there, put the theorem's name in its
`<code>` element, and refresh.

## Tests

    site/test_identity.sh LEAN_REPO SITE_REPO

The faithfulness test. It exports the site folder of site commit `8e741cd` (2026-10-17, the last output
of the original generator), runs `refresh.py --identity --rev v1.1.0` on a copy, and compares. It
passes when the only difference is the added `lean/README.md`, a file that the published sources index
links to and the published folder lacked. `--identity` makes `refresh.py` behave like the original:
it keeps the old footer, skips the bookkeeping, and cuts statements the way the original did.

    python3 -I site/refresh.py REPO SITE_DIR      # twice: the second run prints "files changed: 0"
    python3 -I site/linkcheck.py SITE_DIR         # internal links; refresh runs it too
    python3 -I site/validate_pages.py SITE_DIR    # each Lean page against its raw file, line by line

`validate_pages.py` needs only the site folder. A Lean page is one long line of HTML, so `git diff`
does not show where two versions differ. This script does.

## Files

| file | content |
|---|---|
| `refresh.py` | the entry point |
| `leansrc.py` | tokenizer and declaration parser. Text level, no Lean |
| `declinfo.py` | extent, docstring, statement and section variables of a declaration |
| `leanpage.py` | Lean pages: highlighting, line anchors, identifier links, paper chips |
| `leanindex.py` | sources index and declaration index |
| `panels.py` | Lean panels of the paper page |
| `mapbuild.py` | the map JSON, the map table and the statement blocks |
| `p2m.py` | Prove2Me links |
| `linkcheck.py` | link check |
| `pagelib.py`, `validate_pages.py` | read published Lean pages back and compare them with the sources |
| `lean_page_template.html` | frame of a Lean page |
| `test_identity.sh` | the faithfulness test |

## Limits

- A new entry in `data/curation.json` is not supported. Label, anchor and paper position of an entry
  came from the paper source. `refresh.py` stops with a message.
- The coverage table and the counts in section 5 of `formalization.html` are hand-written.
  `refresh.py` prints a note when they no longer match the curation.
- The pages under `certificates/` are made by hand. `refresh.py` only updates their footer line.
- The original generator also rendered the mathematics with KaTeX and ran a browser self-test.
  Neither is reproduced. The mathematics in `index.html` is stored rendered and is left as it is.
- The original cut the statement of a theorem at a `letI … :=` line, which truncated
  `main_field_form_ramified`. `refresh.py` does not. `--identity` reproduces the old behaviour.
