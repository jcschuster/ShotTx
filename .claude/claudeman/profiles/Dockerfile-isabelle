# Demo container: Elixir 1.20 + Isabelle/HOL + atp_mcp
#
# Design decisions:
#
#  1. Debian base, NOT alpine. Isabelle's bundled Poly/ML and JDK are
#     glibc binaries and do not run on musl. This also gives sane locale
#     behaviour for the BEAM.
#  2. Exactly ONE Elixir installation: the one from the base image, at
#     /usr/local/bin (always on the default PATH). No asdf devcontainer
#     features on top — the old setup had the image's Elixir 1.19 AND an
#     asdf-managed Elixir fighting over PATH, and settings.json pointed
#     at asdf shim paths that didn't exist in every build.
#  3. Elixir 1.20 / OTP 28 — atp_mcp requires `elixir: "~> 1.20"`, which
#     is why `mix escript.install hex atp_mcp` silently failed on the old
#     1.19 image (the launcher swallowed the error with `|| true`).
#  4. The atp_mcp escript is installed at BUILD time to a fixed path
#     (/home/node/.mix/escripts/atp_mcp, on PATH via ENV). No SessionStart
#     install hook, no lazy install race on first MCP connect.
#  5. +fnu and a UTF-8 locale are baked in as image ENV so every process
#     (shells, mix, iex, the escript) inherits them.

# --- Isabelle source stage -----------------------------------------------
# Pull from the official makarius/isabelle image instead of downloading the
# tarball at build time. The TUM distribution server redirects to an HTTP-
# only CDN (dist.isabelle.cit.tum.de:80) that is unreachable from many
# build environments. The Docker Hub image ships identical content with
# system HOL heaps already built (via `isabelle build -o system_heaps -b HOL`),
# so they are included in /home/isabelle/Isabelle and copied below.
ARG ISABELLE_VERSION=Isabelle2025-2
FROM docker.io/makarius/isabelle:${ISABELLE_VERSION} AS isabelle-src

FROM docker.io/library/elixir:1.20-otp-28

ARG ISABELLE_VERSION=Isabelle2025-2

# --- OS packages --------------------------------------------------------
# libfontconfig1/libgomp1/pwgen/rlwrap/unzip/less/perl cover headless
# Isabelle (same set the official Isabelle Docker image installs).
# eprover gives the AtpMcp `local_exec` backend an offline prover to run.
# fd-find installs the binary as `fdfind` on Debian, hence the symlink.
RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates curl git jq less unzip zsh sudo procps \
        ripgrep fd-find fzf \
        libfontconfig1 libgomp1 pwgen rlwrap perl \
        nodejs npm \
        eprover \
    && ln -s "$(command -v fdfind)" /usr/local/bin/fd \
    && apt-get clean && rm -rf /var/lib/apt/lists/*

RUN npm install -g @anthropic-ai/claude-code @ast-grep/cli

# --- Isabelle ------------------------------------------------------------
# Copy from the source stage. The makarius image installs Isabelle at
# /home/isabelle/Isabelle with system heaps inside that directory tree.
COPY --from=isabelle-src /home/isabelle/Isabelle /opt/${ISABELLE_VERSION}
RUN chown -R root:root /opt/${ISABELLE_VERSION}

# --- Locale / BEAM filename encoding -------------------------------------
# +fnu forces the BEAM into unicode filename mode. Without it (e.g. under
# a latin1 locale) the :user device escapes non-latin1 characters such as
# U+2026 as \x{2026} — which is invalid JSON and made the MCP client time
# out on tools/list in the old setup. ELIXIR_ERL_OPTIONS covers
# elixir/iex/mix; ERL_AFLAGS is belt-and-suspenders for anything that
# starts the VM another way (e.g. the escript).
ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8 \
    ELIXIR_ERL_OPTIONS="+fnu" \
    ERL_AFLAGS="+fnu"

# --- Non-root user --------------------------------------------------------
RUN useradd -m -s /bin/zsh node \
    && echo "node ALL=(ALL) NOPASSWD:ALL" > /etc/sudoers.d/node
USER node
WORKDIR /workspace

# Single, deterministic PATH baked into the image. settings.json repeats
# exactly this value (see comment there); the two must stay in sync.
ENV MIX_HOME=/home/node/.mix \
    HEX_HOME=/home/node/.hex \
    SHELL=/bin/zsh \
    PATH="/home/node/.mix/escripts:/opt/${ISABELLE_VERSION}/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/workspace/.claude/claudeman/bin"

# --- Elixir tooling + atp_mcp escript (baked in) --------------------------
RUN mix local.hex --force && mix local.rebar --force \
    && mix escript.install hex atp_mcp --force \
    && test -x /home/node/.mix/escripts/atp_mcp

# NOTE: no Livebook in this image. The container is for claudeman (Claude
# Code + the atp MCP server) and local StarExec work only; the KinoAtpClient
# Livebook demo (examples/demo.livemd) is run on the host — see the README.

# --- Isabelle first-run ---------------------------------------------------
# System HOL heaps arrive prebuilt from the isabelle-src stage (built with
# `-o system_heaps`). This call returns immediately and only serves to
# initialise $ISABELLE_HOME_USER (~/.isabelle) so the server registry
# directory exists before the first demo query.
RUN isabelle build -b HOL

# Sanity checks: fail the build if anything the demo depends on is missing
# from PATH.
RUN elixir --version && mix --version && isabelle version \
    && command -v atp_mcp && command -v eprover
