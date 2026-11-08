# Build the new development in theories/ (the old code in src/ has its own Makefile).

all: Makefile.rocq
	$(MAKE) -f Makefile.rocq

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

clean: Makefile.rocq
	$(MAKE) -f Makefile.rocq cleanall
	rm -f Makefile.rocq Makefile.rocq.conf

.PHONY: all clean
