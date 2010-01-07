EXTRA_DIST = $(wildcard *.v)

check:
	logfile="failures-$$(date -Idate).log"; \
	cat /dev/null > log.tmp; \
	cat /dev/null > "$$logfile"; \
	for f in $(EXTRA_DIST); do \
	  cp "$$f" check_tmp.v; \
	  $(COQC) -R ../src Interval check_tmp.v > output.tmp 2>&1; \
	  return_code=$$?; \
	  if [ $${return_code} -ne 0 ]; then \
	    (echo "*** $$f exited with error code $${return_code}"; cat output.tmp; echo) >> "$$logfile"; \
	    echo "$$f exited with error code $${return_code}" >> log.tmp; \
	  fi; \
	  rm -f check_tmp.v check_tmp.vo check_tmp.glob output.tmp; \
	done; \
	nb=$$(cat log.tmp | wc -l); \
	if [ $$nb -gt 0 ]; then \
	  echo "*** Failures:"; \
	  cat log.tmp; \
	else \
	  rm "$$logfile"; \
	fi; \
	rm log.tmp
