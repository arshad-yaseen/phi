# CLAUDE.md

Code style, safety, performance, and naming rules live in [AGENTS.md](AGENTS.md).
Read that first and follow it for anything inside a source file. This file covers
everything outside the code: what to run, what to commit, and how a release
happens.

## Layout

```
compiler/    the compiler, importable as the `compiler` module
tools/phi/   the binary: argv, dispatch, exit codes
lib/std/     the standard library, shipped as source beside the binary
test/        file tests, one directory per kind
docs/        the design, one document per area
```

## Commands

Zig 0.16.0 or newer, as `build.zig.zon` states.

```
zig build                                     build ./zig-out/bin/phi
zig build test                                unit tests and file tests
zig build test-update                         rewrite what the file tests expect
zig build release                             cross-compile a tree per target
zig fmt --check build.zig compiler tools test what CI checks
```

`test-update` accepts whatever the compiler currently prints. After running it,
read the diff. A golden that changed for a reason you cannot name is a
regression you just recorded as expected.

## After every change

1. `zig build test`. It takes under a second, so there is no reason to skip it.
2. `zig fmt`.
3. Touch `## [Unreleased]` in `CHANGELOG.md`, **only if a user would notice**:
   the language, a diagnostic, the standard library, or the command line.
   Refactors, internals, tests, and CI changes get no entry. The section is a
   draft of the release notes, so follow the rules under `## Changelog`: one
   sentence, and amend the entry already there before adding one beside it.
4. Commit and push **only when asked**, and then wait for CI. This holds
   every time: work stays in the tree until the commit is requested.

## Commit messages

```
area: imperative summary
```

- Lowercase after the colon, imperative mood, no trailing full stop.
- Subject at most 50 characters so `git log --oneline` never wraps. Hard limit 72.
- Blank line, then a body wrapped at 72 explaining **why**. The diff already says
  what changed.
- One logical change per commit.
- A pull request is squashed when it merges, so its title is the subject line
  that lands on `main`. Write it to the rules above rather than as a sentence,
  and give the description the **why** a body would have carried.
- No trailers of any kind. No `Co-Authored-By`, no `Generated with`, no tool or
  assistant attribution. A commit is authored by whoever committed it, and the
  message is for the next reader of `git blame`, not a record of who typed it.

  This holds for everything the repository publishes, not just the commit
  message: pull request titles and descriptions, issue comments, review
  comments, and release notes carry no attribution either. The rule is about
  what the project says, so it does not stop at the commit.

```
check: remove the two-arena rule

The rule refused a second Arena parameter, but nothing else in the
compiler enforced the memory model, so it rejected valid programs while
the rules it belonged to went unchecked. The region checker reimposes it
along with the rest.
```

Conventional Commits (`feat:`, `fix:`, `chore:`) is not used here. It exists to
feed changelog generators, and this changelog is written by hand, so the prefix
would cost the area name and buy nothing.

## Changelog

The changelog is read by someone deciding what an upgrade means, not by the
reviewer of a diff. Every rule here follows from that.

- **An entry is a headline, not documentation.** One sentence, two at the
  most. The diagnostic teaches its details and the design holds the why, so
  an entry that needs a paragraph is trying to be one of those.
- **Amend, never accumulate.** A change that refines something already under
  `[Unreleased]` edits that entry rather than adding a new one. The git log
  is the record of what happened. The changelog is the difference between
  two releases, written once, in its final form.
- **A fix exists only against the last release.** A bug introduced and fixed
  inside one cycle never shipped, so the feature's entry is written as
  though the bug never was. "Used to crash" earns its place only when the
  crash could be seen in a numbered release.
- **Name a diagnostic code only when the code is the news**, a retirement or
  a renumbering someone will search old logs for. An entry that lists codes
  is an index, not a headline.
- **A release section is a story, then lists.** A lede of a few sentences
  says what the release is. Then `### Language`, `### Compiler`,
  `### Command line`, and `### Distribution`, each present only when it has
  entries, and the entries in a section share one shape so the list reads
  in one rhythm.

## Releasing

Versions are `0.MINOR.PATCH`. Before 1.0 a minor release may change the language
in ways that break programs that used to compile, and a patch release only fixes.

### Two channels

Everything published comes out of one pipeline through two doors.

- **Numbered releases**, at `X.Y.Z`. Cut by hand, immutable once pushed, and the
  only thing anyone should build against. This is what a bug report should name
  and what the changelog is written for.
- **Dev builds**, at the `dev` tag. Every commit that reaches `main` and passes
  CI is cross-compiled and published there, under the version it reports:
  `0.2.0-dev.47+7f3a91c9a`. `.github/workflows/dev.yml` replaces the assets each
  time, so `dev` holds the tip of `main` and nothing else.

Dev builds exist so that a report names one commit rather than a branch. They
carry no promise: the next push overwrites them, and they get no notes and no
support. Say so wherever they are offered.

A downloader reads `index.json`, which names the version, the commit, and every
archive with its checksum and size. Two URLs never move:

```
https://github.com/arshad-yaseen/phi/releases/download/dev/index.json
https://github.com/arshad-yaseen/phi/releases/latest/download/index.json
```

**When.** `## [Unreleased]` is the trigger. Entries someone could act on means a
minor. A shipped release that is broken means a patch. Empty means there is
nothing to release, so do not cut one on a schedule.

**How.**

1. Move `[Unreleased]` to `## [X.Y.Z] - YYYY-MM-DD` and add the two link
   definitions at the foot of the file.
2. Set `.version` in `build.zig.zon` to `X.Y.Z`.
3. `zig build release`, as a local smoke test.
4. Commit `release: X.Y.Z`, push `main`, and wait for CI to pass.
5. `git tag -a X.Y.Z -m "Phi X.Y.Z"`.
6. `git push origin X.Y.Z`, on its own.
7. Set `.version` to the next minor, so later builds report `X.Y+1.0-dev.N+hash`.

Four rules, each of which has already cost a release:

- Tag only a commit CI has passed. The workflow runs the same matrix again
  before it publishes, so breaking this now fails loudly rather than quietly,
  but it still spends a tag you cannot take back.
- Push the tag by itself. A branch and a tag in one `git push` loses the tag
  event, and the release workflow never runs.
- Never move a version tag, and never touch a published version's assets. The
  one tag that moves is `dev`, which points at the tip of `main` rather than
  naming a version, and is the only thing the pipeline may overwrite.
- Never hand-edit a published archive or index. Both are written by the
  pipeline, from one commit, and are re-cut rather than repaired.

The tag fires `.github/workflows/release.yml`. It runs CI, then hands off to
`.github/actions/package`, which builds every target, archives them, writes
`SHA256SUMS` and `index.json`, and attaches a provenance attestation tying each
archive to the commit and workflow run that produced it. The notes come from the
`[X.Y.Z]` section of `CHANGELOG.md`, and a tag with no section fails rather than
publishing an empty release. `build.zig` refuses to build when the tag and the
manifest version disagree, so a mistagged release stops before it publishes.

`dev.yml` and `release.yml` share that packaging action, so the two channels
cannot drift into producing differently shaped downloads.

## Versions

`build.zig.zon` holds the next, unreleased version, and is the only place a
version is written. A build standing on the matching tag reports it bare, and
every other build reports something like `0.2.0-dev.47+7f3a91c9a`, so a bug
report names one commit rather than a branch.

`resolveVersion` in `build.zig` derives that from `git describe`, and refuses
two ways of being wrong rather than shipping a version that lies:

- A tree with no history to read reports `0.2.0-dev` and stops. It understates,
  which is the only safe direction: a source archive unpacked without its `.git`
  must never claim to be the release it still precedes.
- A tag standing at or past the manifest version fails the build. Left alone it
  would number every commit on `main` below a release that already exists, and
  every comparison made downstream would read it that way.
