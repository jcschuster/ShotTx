#!/usr/bin/env bash
# Lazy launcher for the atp_mcp escript. Installs the escript on first run
# (or when missing), then execs it. Lets the MCP client succeed on the very
# first connection attempt instead of racing a SessionStart hook.
set -e
ESCRIPT="${HOME}/.asdf/installs/elixir/1.19.5-otp-28/.mix/escripts/atp_mcp"
if [ ! -x "$ESCRIPT" ]; then
  mix escript.install hex atp_mcp --force >/dev/null 2>&1 || true
fi
exec "$ESCRIPT" "$@"
