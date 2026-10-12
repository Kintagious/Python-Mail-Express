#!/usr/bin/env bash
# Runs Python Mail Express on Linux (sets up its own Python environment the first time).
cd "$(dirname "$0")" || exit 1

if [ "$(id -u)" -eq 0 ]; then
    echo "Please run this as your normal user, without sudo:   ./run.sh"
    exit 1
fi

if [ ! -f .venv/.ready ]; then
    echo "First run: setting up Python Mail Express (this takes a few minutes)..."
    if [ -d .venv ] && ! rm -rf .venv 2>/dev/null; then
        echo "An old .venv folder from a sudo run is in the way. Remove it once with:"
        echo "    sudo rm -rf .venv"
        echo "then run ./run.sh again."
        exit 1
    fi
    if ! python3 -m venv .venv; then
        rm -rf .venv
        echo
        echo "Python's venv support is missing. Install it with:"
        echo "    sudo apt install python3-venv"
        echo "then run ./run.sh again."
        exit 1
    fi
    .venv/bin/python -m pip install --upgrade pip || exit 1
    .venv/bin/python -m pip install -r requirements.txt || { echo "Installing the requirements failed (see above)."; exit 1; }
    touch .venv/.ready
    echo "Setup finished."
fi

if ! /sbin/ldconfig -p 2>/dev/null | grep -q "libxcb-cursor.so.0"; then
    echo "Note: if no window appears, install Qt's missing helper with:  sudo apt install libxcb-cursor0"
fi

exec .venv/bin/python express_mail.py "$@"
