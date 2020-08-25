COQC=coqc
COQPARAMS=-R . SNames

MODULES=Morph.vok Var.vok VarEquations.vok Closing.vok ClosingEquations.vok \
	Renaming.vok RenamingEquations.vok Context.vok Term.vok

all: ${MODULES}

%.vos: %.v
	${COQC} -vos ${COQPARAMS} $<

%.vok: %.v
	${COQC} -vok ${COQPARAMS} $<

VarEquations.vok VarEquations.vos: Var.vos

Closing.vok Closing.vos: Var.vos

ClosingEquations.vok ClosingEquations.vos: Var.vos VarEquations.vos Closing.vos

Renaming.vok Renaming.vos: Var.vos Closing.vos

RenamingEquations.vok RenamingEquations.vos: Var.vos Closing.vos VarEquations.vos ClosingEquations Renaming.vos

Context.vok Context.vos: Var.vos

Term.vok Term.vos: Morph.vos Var.vos Renaming.vos VarEquations.vos RenamingEquations.vos

