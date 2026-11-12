# Prove2Me export of the v1.2 theorems

The whole development is published on [Prove2Me](https://prove2.me) as the public tree `TypeDensity`.
The original export, made in October 2026, covered v1.1.0. Its exporter was in the workspace that was
lost in November 2026. The tools here were written on 2026-11-11 to add what v1.2.0 added: the 25 public
theorems of `SurfaceBlowup/Corollaries/Nonneg.lean`, `SurfaceBlowup/Corollaries/RationalForm.lean` and
`Tests/PadicInt.lean`, and one definition module, `TypeDensity_Tests_PadicInt`.

| file | what it is |
|---|---|
| `build_bundle.py` | writes the upload bundle from the sources of tag `v1.2.0` and the platform's exported files |
| `upload.py` | sends the bundle to the platform, one step at a time, and can resume |
| `FORMAT.md` | the conventions of the original exporter, read off the public export, which the bundle follows |

## Environment

The platform compiles in its environment "Mathlib 0df444a (Lean v4.33.1)". This repository moved to
Lean v4.35.0 in v1.3.0, so uploads come from tag `v1.2.0`, the last version that compiles there.

## Work directory

Both scripts work in a directory outside the tracked files, called `WORK` below. `scratch/prove2me` in
a clone will do: `.gitignore` excludes `scratch/`. Nothing in `WORK` belongs in the repository. The
platform's files are the platform's. The upload state holds job and submission ids of the account that
uploads.

    mkdir -p WORK/src-v1.2.0 WORK/validate/Definitions WORK/validate/Theorems
    git archive v1.2.0 | tar -x -C WORK/src-v1.2.0

The platform publishes its trees as Lean files at `github.com/prove2me/formalpedia`. Fetch the
`TypeDensity` files of the environment with one sparse clone. No credentials are needed.

    git clone --filter=blob:none --no-checkout https://github.com/prove2me/formalpedia.git WORK/formalpedia
    git -C WORK/formalpedia sparse-checkout init --no-cone
    git -C WORK/formalpedia sparse-checkout set --no-cone \
      '/envs/0df444a/Definitions/Def_TypeDensity_*' '/envs/0df444a/Theorems/Thm_TypeDensity_*'
    git -C WORK/formalpedia checkout fd877e9fa8b7c633cc697db64705bcb978c68e97
    cp WORK/formalpedia/envs/0df444a/Definitions/*.lean WORK/validate/Definitions/
    cp WORK/formalpedia/envs/0df444a/Theorems/*.lean WORK/validate/Theorems/

Commit `fd877e9f` is the snapshot the bundle was built against: 36 definition modules and 1034 theorem
statements, the tree before this upload. Use `main` instead to build against the newest snapshot.

## Building the bundle

    python3 -I tools/prove2me/build_bundle.py WORK

It writes `WORK/bundle/` and `WORK/ORDER.json`: 51 steps, a statement and a solution for each of the 25
theorems and one definition module. It compiles nothing and uses no network. With the inputs above it
reproduces the 51 files that were uploaded: their SHA-256 hashes equal the ones the uploader recorded.
Ten titles were written by hand before the upload. They are the table `TITLES` in the script.

`ORDER.padicint-as-module.json` is another reading of `Tests/PadicInt.lean` (`FORMAT.md`, section 8).
It was not used.

## Validating locally

`WORK/validate` becomes a Lake project that mirrors the platform's environment:

- `lean-toolchain`: `leanprover/lean4:v4.33.1`.
- `lakefile.lean`: a package with the option `autoImplicit false`, Mathlib required at
  `0df444a360eaa60ab8c11dca51a86af692955474`, and the libraries `Definitions`, `Theorems`, `Solutions`.
- `lake-manifest.json`: the manifest of tag `v1.2.0` with the package name changed to the lakefile's,
  so that Mathlib's dependencies are pinned to the same revisions.

Stage the bundle next to the platform's files and build:

    mkdir -p WORK/validate/Solutions
    cp WORK/bundle/definitions/*.lean WORK/validate/Definitions/
    cp WORK/bundle/problems/*.lean WORK/validate/Theorems/
    cp WORK/bundle/solutions/*.lean WORK/validate/Solutions/
    cd WORK/validate && lake exe cache get && lake build Definitions Theorems Solutions

The statements import nearly the whole tree, so this compiles about a thousand small files. Imported
statements are `sorry` stubs, as they are on the server. On 2026-11-11 all 51 steps compiled. Each
`solution` had exactly the type of its statement. That was checked with one generated file per theorem,
`example : type_of% @<statement> := @solution`, and a comparison of the two types as expressions.

## Uploading

    python3 -I tools/prove2me/upload.py --order WORK/ORDER.json --dry-run
    python3 -I tools/prove2me/upload.py --order WORK/ORDER.json

The dry run prints every request and reads no key. A real run reads the API key from
`~/.config/prove2me/api_key`. Create it in the account menu of prove2.me and give the file mode 600. The
key is exchanged for a one-hour token, and both are sent only to `https://prove2.me/api/v1/`. The
script writes `upload_state.<variant>.json` next to the order file and resumes from it after an
interruption.

## What was uploaded

On 2026-11-11 the platform accepted all 51 steps: 25 statements and one definition module published,
25 solutions accepted. The tree then had 37 definition modules and 1059 theorems. The public pages are
`https://prove2.me/theorems/<id>`. The ids are in `data/prove2me_nodes.json` of the companion site, on
the nodes marked `"added": "2026-11-11"`.

`FORMAT.md`, section 8, left two points open. Both are settled. The platform accepts an
`attribute [local instance]` line in a preamble: the five theorems of `Tests/PadicInt.lean` depend on
it. Lean generates the instance name `instFiniteResidueFieldPadicInt_tests`: the validation project
checked it.
