COQC=coqc
COQDEP=coqdep
THEORIES=theories
VFILES=$(wildcard $(THEORIES)/*.v)
VOFILES=$(VFILES:.v=.vo)

all: $(VOFILES)

%.vo: %.v
	$(COQC) -Q $(THEORIES) ECCIC256 $<

clean:
	rm -f $(THEORIES)/*.vo $(THEORIES)/*.glob

.PHONY: all clean
