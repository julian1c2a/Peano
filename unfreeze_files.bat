@echo off
REM unfreeze_files.bat
REM Descongela archivos del proyecto permitiendo que sean commiteables nuevamente

echo Descongelando archivos del proyecto Peano...
echo.

REM Archivos de documentación principales
git update-index --no-assume-unchanged README.md
git update-index --no-assume-unchanged REFERENCE.md
git update-index --no-assume-unchanged CURRENT-STATUS-PROJECT.md
git update-index --no-assume-unchanged CHANGELOG.md

REM Archivos de configuración
git update-index --no-assume-unchanged .gitignore
git update-index --no-assume-unchanged .gitattributes
git update-index --no-assume-unchanged lakefile.lean
git update-index --no-assume-unchanged lean-toolchain

REM Módulos principales
git update-index --no-assume-unchanged Peano.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatLib.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatAxioms.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatStrictOrder.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatOrder.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatMaxMin.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatWellFounded.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatAdd.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatSub.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatMul.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatDiv.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatArith.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatPrimes.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatPow.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatFactorial.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatBinom.lean
git update-index --no-assume-unchanged PeanoNatLib\PeanoNatNewtonBinom.lean

echo.
echo Archivos descongelados exitosamente
echo.
echo Los archivos ahora pueden ser commiteados normalmente
