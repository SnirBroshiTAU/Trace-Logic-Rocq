./clean.ps1
coqc -compat 8.20 -Q src Project ./src/Language.v
coqc -compat 8.20 -Q src Project ./src/LanguageWithLines.v
coqc -compat 8.20 -Q src Project ./src/TraceLogic2019.v
coqc -compat 8.20 -Q src Project ./src/TraceLogic2020.v
coqc -compat 8.20 -Q src Project ./src/TraceLogic2020WithLines.v
