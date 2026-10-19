# Self-contained Shot build for SystemOnTPTP. The result needs no Erlang/Elixir
# on the host: the release bundles the Erlang runtime (ERTS).
#
#   podman build --target dist -o dist .      # -> dist/Shot---<version>.tgz
#   podman build --target check .             # smoke test on a host without Erlang
#
# Source archive to ship alongside:
#   git archive --prefix=Shot---<version>-src/ -o dist/Shot---<version>-src.tgz HEAD
#
# The bundled ERTS links against the builder's glibc, so the package runs only on
# hosts with that glibc or newer. Pick the oldest builder the target can take, e.g.
#   --build-arg BUILDER=docker.io/hexpm/elixir:<elixir>-erlang-<otp>-debian-bullseye-<date>
#   --build-arg RUNTIME=docker.io/library/debian:bullseye-slim
# (glibc 2.31). The defaults below are Debian trixie (glibc 2.41).

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
RUN mix release \
 && VERSION=$(grep -m1 '@version "' mix.exs | cut -d'"' -f2) \
 && mkdir -p /out \
 && cp -a _build/prod/rel/shot_tx "/out/Shot---${VERSION}" \
 && tar -C /out -czf "/out/Shot---${VERSION}.tgz" "Shot---${VERSION}"

# Runs the package on a system without Erlang; fails the build if it misbehaves.
FROM ${RUNTIME} AS check
COPY --from=build /out /opt/shot
RUN set -e; cd /opt/shot/Shot---*/; \
    printf 'thf(p_t,type,p:$o).\nthf(c,conjecture,p | ~p).\n' > /tmp/t.p; \
    printf 'thf(p_t,type,p:$o).\nthf(c,conjecture,p).\n' > /tmp/c.p; \
    bin/shot -V; \
    bin/shot --szs --proof -t 10000 /tmp/t.p | tee /tmp/out; \
    grep -q '^% SZS status Theorem for t.p$' /tmp/out; \
    bin/shot --szs -t 10000 /tmp/c.p | grep -q '^% SZS status CounterSatisfiable for c.p$'; \
    ! grep -v '^%' /tmp/out

FROM scratch AS dist
COPY --from=build /out/*.tgz /
