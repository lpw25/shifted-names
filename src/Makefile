COQC=coqc
COQPARAMS=-R . SNames

MODULES=Morph.vok Index.vok Name.vok Level.vok Var.vok \
	Var2.vok Trm.vok Renaming2.vok Context.vok Relative.vok

all: ${MODULES}

%.vos: %.v
	${COQC} -vos ${COQPARAMS} $<

%.vok: %.v
	${COQC} -vok ${COQPARAMS} $<

Var.vok Var.vos: Morph.vos

Index.vok Index.vos: Morph.vos

Name.vok Name.vos: Morph.vos Index.vos

Level.vok Level.vos: Morph.vos

Var2.vok Var2.vos: Morph.vos Index.vos Name.vos Level.vos

Trm.vok Trm.vos: Morph.vos Trm.vos

Renaming2.vok Renaming2.vos: Morph.vos Var2.vos

Context.vok Context.vos: Var.vos

Relative.vok Relative.vos: Morph.vos Var.vos Context.vos

