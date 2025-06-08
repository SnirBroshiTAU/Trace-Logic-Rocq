./clean.ps1
coqc -Q src Project ./src/Language.v
coqc -Q src Project ./src/LanguageWithLines.v
coqc -Q src Project ./src/TraceLogic2019.v
coqc -Q src Project ./src/TraceLogic2020.v
coqc -Q src Project ./src/TraceLogic2020WithLines.v
