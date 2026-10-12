#!/usr/bin/env bash
# Runs Python Mail Express on Linux (sets up its own Python environment the first time).
cd "$(dirname "$0")" || exit 1
if [ ! -x .venv/bin/python ]; then
    echo "First run: setting up (this takes a minute)..."
    python3 -m venv .venv || { echo "Please install python3-venv (e.g. sudo apt install python3-venv)"; exit 1; }
    .venv/bin/pip install --upgrade pip
    .venv/bin/pip install -r requirements.txt || exit 1
fi
exec .venv/bin/python express_mail.py "$@"
