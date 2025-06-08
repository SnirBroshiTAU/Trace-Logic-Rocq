./clean.sh
coqc $(< ./_CoqProject) ./src/Language.v
coqc $(< ./_CoqProject) ./src/LanguageWithLines.v
coqc $(< ./_CoqProject) ./src/TraceLogic2019.v
coqc $(< ./_CoqProject) ./src/TraceLogic2020.v
coqc $(< ./_CoqProject) ./src/TraceLogic2020WithLines.v
