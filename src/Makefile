COQC=coqc
COQPARAMS=-R . SNames

MODULES=Label.vok Var.vok RawRenaming.vok RawRenamingEquations.vok

all: ${MODULES}

%.vos: %.v
	${COQC} -vos ${COQPARAMS} $<

%.vok: %.v
	${COQC} -vok ${COQPARAMS} $<

Var.vok Var.vos: Label.vos

RawRenaming.vok RawRenaming.vos: Label.vos Var.vos

RawRenamingEquations.vok RawRenamingEquations.vos: Label.vos Var.vos RawRenaming.vos
