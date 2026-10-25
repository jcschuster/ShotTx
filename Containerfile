# Self-contained Shot build for SystemOnTPTP. The result needs no Erlang/Elixir
# on the host: the release bundles the Erlang runtime (ERTS).
#
#   podman build --target dist -o dist .      # -> dist/Shot---<version>.tgz
#                                             #    dist/Shot---<version>-starexec.tgz
#   podman build --target check .             # smoke test on a host without Erlang
#
# The first archive unpacks into Shot---<version>/ (SystemOnTPTP); the second
# has bin/ at its top level, as StarExec requires (bin/starexec_run_default).
#
# Source archive to ship alongside:
#   git archive --prefix=Shot---<version>-src/ -o dist/Shot---<version>-src.tgz HEAD
#
# The bundled ERTS links against the builder's glibc, so the package runs only on
# hosts with that glibc or newer. The default (Debian trixie) build needs
# GLIBC_2.38, which the SystemOnTPTP host (Ubuntu 24.04, glibc 2.39) provides.
# For an older host pick an older builder, e.g.
#   --build-arg BUILDER=docker.io/hexpm/elixir:<elixir>-erlang-<otp>-debian-bullseye-<date>
#   --build-arg RUNTIME=docker.io/library/debian:bullseye-slim
# (glibc 2.31). To smoke-test on the SystemOnTPTP image instead:
#   --build-arg RUNTIME=docker.io/library/ubuntu:24.04

ARG BUILDER=docker.io/library/elixir:1.20-otp-29
ARG RUNTIME=docker.io/library/debian:trixie-slim

FROM ${BUILDER} AS build
ENV MIX_ENV=prod LANG=C.UTF-8
WORKDIR /src
RUN mix local.hex --force && mix local.rebar --force
COPY mix.exs mix.lock ./
RUN mix deps.get --only prod && mix deps.compile
COPY lib lib
COPY rel rel
# libsctp (LGPL-2.1): ERTS dlopens it at boot and, where it is missing, prints a
# warning on stdout. bin/shot puts lib/ on LD_LIBRARY_PATH.
RUN mix release \
 && VERSION=$(grep -m1 '@version "' mix.exs | cut -d'"' -f2) \
 && mkdir -p /out \
 && cp -a _build/prod/rel/shot_tx "/out/Shot---${VERSION}" \
 && cp -L "/usr/lib/$(uname -m)-linux-gnu/libsctp.so.1" "/out/Shot---${VERSION}/lib/" \
 && tar -C /out -czf "/out/Shot---${VERSION}.tgz" "Shot---${VERSION}" \
 && tar -C "/out/Shot---${VERSION}" -czf "/out/Shot---${VERSION}-starexec.tgz" .

# Runs the package on a system without Erlang, libsctp or a locale; fails the
# build if it misbehaves. The `⊥` check catches latin1 stdout.
FROM ${RUNTIME} AS check
COPY --from=build /out /opt/shot
RUN set -e; cd /opt/shot/Shot---*/; \
    printf 'thf(p_t,type,p:$o).\nthf(c,conjecture,p | ~p).\n' > /tmp/t.p; \
    printf 'thf(p_t,type,p:$o).\nthf(c,conjecture,p).\n' > /tmp/c.p; \
    bin/shot -V; \
    bin/shot --szs --proof -t 10000 /tmp/t.p | tee /tmp/out; \
    grep -q '^% SZS status Theorem for t.p$' /tmp/out; \
    grep -q '⊥' /tmp/out; \
    bin/shot --szs -t 10000 /tmp/c.p | grep -q '^% SZS status CounterSatisfiable for c.p$'; \
    ! grep -v '^%' /tmp/out; \
    STAREXEC_WALLCLOCK_LIMIT=10 bin/starexec_run_default /tmp/t.p | grep -q '^% SZS status Theorem for t.p$'; \
    ! ls erl_crash.dump core 2>/dev/null

FROM scratch AS dist
COPY --from=build /out/*.tgz /
