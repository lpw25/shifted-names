COQC=coqc
COQPARAMS=-R . SNames

MODULES=Label.vok Var.vok VarEquations.vok Closing.vok ClosingEquations.vok \
	Renaming.vok RenamingEquations.vok Context.vok Term.vok Morph.vok

all: ${MODULES}

%.vos: %.v
	${COQC} -vos ${COQPARAMS} $<

%.vok: %.v
	${COQC} -vok ${COQPARAMS} $<

Var.vok: Label.vos

VarEquations.vok VarEquations.vos: Label.vos Var.vos

Closing.vok Closing.vos: Label.vos Var.vos

ClosingEquations.vok ClosingEquations.vos: Label.vos Var.vos VarEquations.vos Closing.vos

Renaming.vok Renaming.vos: Label.vos Var.vos Closing.vos

RenamingEquations.vok RenamingEquations.vos: Label.vos Var.vos Closing.vos VarEquations.vos ClosingEquations Renaming.vos

Context.vok Context.vos: Var.vos

Term.vok Term.vos: Morph.vos Var.vos Renaming.vos VarEquations.vos RenamingEquations.vos

