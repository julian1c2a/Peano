@echo off
REM freeze_files.bat
REM Congela archivos del proyecto marcándolos como assume-unchanged en git
REM Esto evita que cambios locales sean commiteados accidentalmente

echo Congelando archivos del proyecto Peano...
echo.

REM Archivos de documentación principales
git update-index --assume-unchanged README.md
git update-index --assume-unchanged REFERENCE.md
git update-index --assume-unchanged CURRENT-STATUS-PROJECT.md
git update-index --assume-unchanged CHANGELOG.md

REM Archivos de configuración
git update-index --assume-unchanged .gitignore
git update-index --assume-unchanged .gitattributes
git update-index --assume-unchanged lakefile.lean
git update-index --assume-unchanged lean-toolchain

REM Módulos principales
git update-index --assume-unchanged Peano.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatLib.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatAxioms.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatStrictOrder.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatOrder.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatMaxMin.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatWellFounded.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatAdd.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatSub.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatMul.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatDiv.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatArith.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatPrimes.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatPow.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatFactorial.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatBinom.lean
git update-index --assume-unchanged PeanoNatLib\PeanoNatNewtonBinom.lean

echo.
echo Archivos congelados exitosamente
echo.
echo Para descongelar, ejecuta: unfreeze_files.bat
