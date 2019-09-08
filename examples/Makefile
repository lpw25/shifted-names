COQC=coqc
COQPARAMS=-R ../src SNames

MODULES=Lambda.vo

all: ${MODULES}

%.vo: %.v
	${COQC} ${COQPARAMS} $<

