COQC=coqc
COQPARAMS=-R . SNames

MODULES=Morph.vo Var.vo Context.vo Relative.vo

all: ${MODULES}

%.vo: %.v
	${COQC} ${COQPARAMS} $<

Var.vo: Morph.vo

Context.vo: Var.vo

Relative.vo: Morph.vo Var.vo Context.vo

