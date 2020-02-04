COQC=coqc
COQPARAMS=-R . SNames

MODULES=Morph.vok Var.vok Var2.vok Renaming2.vok Context.vok Relative.vok

all: ${MODULES}

%.vos: %.v
	${COQC} -vos ${COQPARAMS} $<

%.vok: %.v
	${COQC} -vok ${COQPARAMS} $<

Var.vok Var.vos: Morph.vos

Var2.vok Var2.vos: Morph.vos

Renaming2.vok Renaming2.vos: Morph.vos Var2.vos

Context.vok Context.vos: Var.vos

Relative.vok Relative.vos: Morph.vos Var.vos Context.vos

