COQC=coqc
COQPARAMS=-R . SNames

MODULES=Morph.vo Var.vo Var2.vo Renaming2.vo Context.vo Relative.vo

all: ${MODULES}

%.vo: %.v
	${COQC} ${COQPARAMS} $<

Var.vo: Morph.vo

Var2.vo: Morph.vo

Renaming2.vo: Morph.vo Var2.vo

Context.vo: Var.vo

Relative.vo: Morph.vo Var.vo Context.vo

