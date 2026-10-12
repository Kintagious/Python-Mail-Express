@echo off
REM Builds ExpressMail.exe (a single file in the "dist" folder).
REM Needs Python 3.10+ from python.org with "Add python.exe to PATH" ticked.

cd /d "%~dp0"
python -m pip install --upgrade pip
python -m pip install -r requirements.txt pyinstaller
python express_mail.py --make-icon
python -m PyInstaller --noconfirm --onefile --windowed --name ExpressMail --icon express_mail.ico express_mail.py

echo.
echo Done. Your program is in: %~dp0dist\ExpressMail.exe
pause
