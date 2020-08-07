COQC=coqc
COQPARAMS=-R . SNames

MODULES=Morph.vok Var.vok VarEquations.vok Renaming.vok RenamingEquations.vok \
	Context.vok Term.vok

all: ${MODULES}

%.vos: %.v
	${COQC} -vos ${COQPARAMS} $<

%.vok: %.v
	${COQC} -vok ${COQPARAMS} $<

Var.vok Var.vos: Morph.vos

VarEquations.vok VarEquations.vos: Morph.vos Var.vos

Renaming.vok Renaming.vos: Morph.vos Var.vos

RenamingEquations.vok RenamingEquations.vos: Morph.vos Var.vos VarEquations.vos Renaming.vos

Context.vok Context.vos: Morph.vos Var.vos

Term.vok Term.vos: Morph.vos Var.vos Renaming,vos VarEquations.vos RenamingEquations.vos

