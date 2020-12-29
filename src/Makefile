COQC=coqc
COQPARAMS=-R . SNames

MODULES=Label.vok Var.vok VarEquations.vok \
	RawRenaming.vok RawRenamingEquations.vok \
	Renaming.vok RenamingEquations.vok \
	Context.vok Term.vok Morph.vok

all: ${MODULES}

%.vos: %.v
	${COQC} -vos ${COQPARAMS} $<

%.vok: %.v
	${COQC} -vok ${COQPARAMS} $<

Var.vok Var.vos: Label.vos

VarEquations.vok VarEquations.vos: Label.vos Var.vos

RawRenaming.vok RawRenaming.vos: Label.vos Var.vos

RawRenamingEquations.vok RawRenamingEquations.vos: Label.vos Var.vos VarEquations.vos RawRenaming.vos

Renaming.vok Renaming.vos: Label.vos Var.vos VarEquations.vos RawRenaming.vos

RenamingEquations.vok RenamingEquations.vos: Label.vos Var.vos Closing.vos VarEquations.vos RawRenaming.vos RawRenamingEquations.vos Renaming.vos

Context.vok Context.vos: Var.vos

Term.vok Term.vos: Morph.vos Var.vos Renaming.vos VarEquations.vos RenamingEquations.vos

