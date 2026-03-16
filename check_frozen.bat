@echo off
REM check_frozen.bat
REM Verifica qué archivos están congelados (assume-unchanged)

echo Verificando archivos congelados en el proyecto Peano...
echo.
echo Archivos marcados como assume-unchanged:
echo ==========================================
git ls-files -v | findstr /R "^h"
echo.
echo (Los archivos con 'h' al inicio están congelados)
