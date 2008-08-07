PACKAGE=interval
VERSION=0.8

##########################
#                        #
# Variables definitions. #
#                        #
##########################

OPT=
COQFLAGS=-q $(OPT) $(COQLIBS) $(OTHERFLAGS) $(COQ_XML)
COQC=$(COQBIN)coqc
COQDOC=$(COQBIN)coqdoc
COQDEP=$(COQBIN)coqdep -c
DISTDIR=$(PACKAGE)-$(VERSION)

#########################
#                       #
# Libraries definition. #
#                       #
#########################

OCAMLLIBS=-I .
COQLIBS=-I .

###################################
#                                 #
# Definition of the "all" target. #
#                                 #
###################################

VFILES=bigint_carrier.v\
  bisect.v\
  definitions.v\
  float_sig.v\
  generic_ops.v\
  generic_proof.v\
  generic.v\
  interval.v\
  interval_float.v\
  interval_float_full.v\
  missing.v\
  specific_ops.v\
  specific_sig.v\
  stdz_carrier.v\
  tactics.v\
  transcend.v\
  xreal.v\
  xreal_derive.v
VOFILES=$(VFILES:.v=.vo)
VIFILES=$(VFILES:.v=.vi)
GFILES=$(VFILES:.v=.g)
HTMLFILES=$(VFILES:.v=.html)
GHTMLFILES=$(VFILES:.v=.g.html)

all: $(VOFILES)

html: $(HTMLFILES)

all.ps: $(VFILES)
	$(COQDOC) -ps -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

all-gal.ps: $(VFILES)
	$(COQDOC) -ps -g -o $@ `$(COQDEP) -sort -suffix .v $(VFILES)`

####################
#                  #
# Special targets. #
#                  #
####################

.PHONY: all opt byte archclean clean install depend html

.SUFFIXES: .v .vo .html .tex

.v.vo:
	$(COQC) $(COQDEBUG) $(COQFLAGS) $*

.v.tex:
	$(COQDOC) -latex $< -o $@

.v.html:
	$(COQDOC) -html $< -o $@

byte:
	$(MAKE) all "OPT="

opt:
	$(MAKE) all "OPT=-opt"

include .depend

.depend depend:
	rm -f .depend
	$(COQDEP) -i $(COQLIBS) $(VFILES) >.depend
	$(COQDEP) $(COQLIBS) -suffix .html $(VFILES) >>.depend

install:
	mkdir -p `$(COQC) -where`/user-contrib
	cp -f $(VOFILES) `$(COQC) -where`/user-contrib

clean:
	rm -f $(VOFILES) $(VIFILES) $(GFILES) *~
	rm -f all.ps all-gal.ps $(HTMLFILES) $(GHTMLFILES)

dist:
	mkdir $(DISTDIR)
	cp $(VFILES) Makefile README COPYING $(DISTDIR)
	tar czf $(DISTDIR).tar.gz $(DISTDIR)
	rm -r $(DISTDIR)
