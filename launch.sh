#!/usr/bin/env bash
set -euo pipefail

APP_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
pkill -f "$APP_DIR/desktop_todo.py" >/dev/null 2>&1 || true
setsid python3 "$APP_DIR/desktop_todo.py" >/tmp/daily-todo.log 2>&1 &
