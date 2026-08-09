FROM docker.io/library/elixir:1.20-otp-28

# --- OS packages --------------------------------------------------------
# eprover gives the AtpMcp `local_exec` backend an offline prover to run.
# fd-find installs the binary as `fdfind` on Debian, hence the symlink.
RUN apt-get update && apt-get install -y --no-install-recommends \
    ca-certificates curl git jq less unzip zsh sudo procps \
    ripgrep fd-find fzf \
    nodejs npm \
    eprover \
    && ln -s "$(command -v fdfind)" /usr/local/bin/fd \
    && apt-get clean && rm -rf /var/lib/apt/lists/*

RUN npm install -g @anthropic-ai/claude-code @ast-grep/cli

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
WORKDIR /workspaces/ShotTx

# Single, deterministic PATH baked into the image. .claude/settings.json
# repeats exactly this value (see comment there); the two must stay in
# sync, and both must match the workspaceFolder in devcontainer.json.
ENV MIX_HOME=/home/node/.mix \
    HEX_HOME=/home/node/.hex \
    SHELL=/bin/zsh \
    PATH="/home/node/.mix/escripts:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/workspaces/ShotTx/.claude/claudeman/bin"

# --- Elixir tooling + atp_mcp escript (baked in) --------------------------
RUN mix local.hex --force && mix local.rebar --force \
    && mix escript.install hex atp_mcp --force \
    && test -x /home/node/.mix/escripts/atp_mcp

# Optional: Livebook for the KinoAtpClient smart-cell demo. Comment out to
# slim the image / speed up the build. Run inside the container with:
#   livebook server --ip 0.0.0.0 --port 8080 examples/demo.livemd
RUN mix escript.install hex livebook --force

# Sanity checks: fail the build if anything the demo depends on is missing
# from PATH.
RUN elixir --version && mix --version && command -v atp_mcp && command -v eprover
