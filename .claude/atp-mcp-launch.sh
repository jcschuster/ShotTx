#!/usr/bin/env bash
# Lazy launcher for the atp_mcp escript. Installs the escript on first run
# (or when missing), then execs it. Lets the MCP client succeed on the very
# first connection attempt instead of racing a SessionStart hook.
set -e
# Force a UTF-8 locale: under latin1 native encoding the BEAM :user device
# escapes non-latin1 chars (e.g. U+2026 …) as \x{2026}, which is not valid
# JSON and causes the MCP client to time out on tools/list.
export LANG=C.UTF-8
export LC_ALL=C.UTF-8
ESCRIPT="$(find "${HOME}/.asdf/installs/elixir" -name "atp_mcp" -path "*/.mix/escripts/*" 2>/dev/null | head -1)"
if [ -z "$ESCRIPT" ]; then
  ESCRIPT="${HOME}/.asdf/installs/elixir/1.20.1-otp-29/.mix/escripts/atp_mcp"
fi
if [ ! -x "$ESCRIPT" ]; then
  mix escript.install hex atp_mcp --force >/dev/null 2>&1 || true
  ESCRIPT="$(find "${HOME}/.asdf/installs/elixir" -name "atp_mcp" -path "*/.mix/escripts/*" 2>/dev/null | head -1)"
fi
exec "$ESCRIPT" "$@"
