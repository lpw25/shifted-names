COQC=coqc
COQPARAMS=-R . SNames

MODULES=Morph.vok Var.vok Context.vok \
	IIndex.vok IName.vok ILevel.vok IVar.vok \
	Term.vok

all: ${MODULES}

%.vos: %.v
	${COQC} -vos ${COQPARAMS} $<

%.vok: %.v
	${COQC} -vok ${COQPARAMS} $<

Var.vok Var.vos: Morph.vos

Context.vok Context.vos: Morph.vos Var.vos

IIndex.vok IIndex.vos: Morph.vos Var.vos

IName.vok IName.vos: Morph.vos Var.vos IIndex.vos

ILevel.vok ILevel.vos: Morph.vos Var.vos

IVar.vok IVar.vos: Morph.vos Var.vos IIndex.vos IName.vos ILevel.vos

Term.vok Term.vos: Morph.vos Var.vos IIndex.vos IName.vos ILevel.vos IVar.vos

