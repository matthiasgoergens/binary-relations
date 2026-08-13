Vendored from https://github.com/matthiasgoergens/tapecheck (MIT) at
`26d3dcd` (master, 2026-08-13; refreshed from `b430a44`), trees `engine/`,
`tape/`, `vendor/`, plus `laws/` which is this project. Upstream's own
`vendor/upstream.lock` records the commits its vendored Jane Street code is
patched from.

**Why a copy and not a git submodule.** A submodule would be the better shape
for the code, but it does not work here, and it fails for the same root cause
as everything else on this branch. `laws/` has to sit *inside* tapecheck's dune
scope, because `tape_engine` is a private library and dune will not let another
project see it. A submodule is a separate repository, so files belonging to
this project cannot be committed inside it. The copy exists precisely so that
`laws/` can live there. If tapecheck's libraries gain `public_name`s — which is
what [splittable_random#2](https://github.com/janestreet/splittable_random/pull/2)
blocks — then neither the copy nor the submodule is needed at all, because
`laws/` moves to `test/` and depends on an ordinary installed library.

Vendored rather than depended on because tapecheck is not installable as an
opam package: its libraries have no `public_name`, and cannot have one until
the `splittable_random` fork carrying `For_tape.attach` lands upstream
(janestreet/splittable_random#2). Its own `vendor/` contains base_quickcheck,
ppx_quickcheck and splittable_random, all Jane Street, MIT.

This directory has its own `dune-project` on purpose: it puts the vendored
`base_quickcheck` in a separate dune scope, so it does not collide with the
installed one that `Core` pulls in for `test/` and `incr/`. See NOTES.md.
