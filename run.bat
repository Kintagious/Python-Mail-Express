@echo off
REM Runs Express Mail straight from source (installs what it needs the first time).
cd /d "%~dp0"
python -c "import PySide6" 2>nul || python -m pip install -r requirements.txt
start "" pythonw express_mail.py
