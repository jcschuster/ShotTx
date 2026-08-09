#!/usr/bin/env bash
# Launcher for the atp_mcp MCP server.
#
# The escript is baked into the image at /home/node/.mix/escripts/atp_mcp
# (on PATH), so there is nothing to install at run time. This script only:
#
#   1. writes an OTP sys.config configuring the local_exec backend, and
#   2. execs atp_mcp on stdio.
#
# On (1): the escript bakes its config at build time and cannot read this
# project's config.exs, so backend settings are injected at runtime via a
# sys.config passed through ERL_FLAGS.
set -euo pipefail

# Defensive re-export: the image ENV already sets all of these, but MCP
# servers can be spawned with a reduced environment. Under a latin1 locale
# the BEAM's :user device escapes non-latin1 chars (e.g. U+2026) as
# \x{2026}, which is invalid JSON and times out the MCP client.
export LANG=C.UTF-8 LC_ALL=C.UTF-8
export ELIXIR_ERL_OPTIONS="${ELIXIR_ERL_OPTIONS:-+fnu}"
export ERL_AFLAGS="${ERL_AFLAGS:-+fnu}"

# Self-locating: everything is derived from this script's own path, so the
# launcher keeps working wherever the repo is mounted. A previous version
# hardcoded /workspace and broke when the mount moved.
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "${SCRIPT_DIR}")"

# The escript lives on the image PATH, but MCP servers may be spawned with
# a reduced environment; make sure the escripts dir is present either way.
export PATH="/home/node/.mix/escripts:${PATH}"

# OTP -config wants the path WITHOUT the .config suffix; the file itself
# must be "${SYS_CONFIG_BASE}.config". Kept outside the repo so it never
# lands in git.
CONFIG_DIR="${HOME}/.atp-mcp"
SYS_CONFIG_BASE="${CONFIG_DIR}/atp_mcp_sys"

# Erlang term file consumed by `erl -config`. Values must be binaries
# (<<"...">>), not charlists, to match what AtpClient.Config expects.
mkdir -p "${CONFIG_DIR}"
umask 077
cat > "${SYS_CONFIG_BASE}.config" <<EOF
[{atp_client,[
  {local_exec,[{binary,<<"eprover">>},{args,[<<"--auto">>,<<"--tstp-format">>]},{cpu_timeout_s,10}]}
]}].
EOF

if ! command -v eprover > /dev/null 2>&1; then
  echo "atp-mcp-launch: WARNING: 'eprover' not on PATH; the local_exec" \
       "backend will fail" >&2
fi

cd "${PROJECT_DIR}"

# Feeds the sys.config above to the escript's BEAM. ERL_FLAGS is separate
# from the image-wide ERL_AFLAGS (+fnu), which still applies.
export ERL_FLAGS="${ERL_FLAGS:+${ERL_FLAGS} }-config ${SYS_CONFIG_BASE}"

exec atp_mcp "$@"
