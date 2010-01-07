FILES = \
	Interval_bigint_carrier.v \
	Interval_bisect.v \
	Interval_definitions.v \
	Interval_float_sig.v \
	Interval_generic_ops.v \
	Interval_generic_proof.v \
	Interval_generic.v \
	Interval_interval.v \
	Interval_interval_float.v \
	Interval_interval_float_full.v \
	Interval_missing.v \
	Interval_specific_ops.v \
	Interval_specific_sig.v \
	Interval_stdz_carrier.v \
	Interval_tactic.v \
	Interval_transcend.v \
	Interval_xreal.v \
	Interval_xreal_derive.v

data_DATA = $(FILES:=o)
EXTRA_DIST = $(FILES)
CLEANFILES = $(FILES:=o) $(FILES:=d) $(FILES:.v=.glob)

datadir = $(libdir)

.v.vo:
	@echo COQC $<
	@$(COQC) $(COQRFLAG) -dont-load-proofs $<

.v.vd:
	@echo COQDEP $<
	@$(COQDEP) -I . $< > $@

SUFFIXES = .v .vo .vd

-include $(FILES:=d)
