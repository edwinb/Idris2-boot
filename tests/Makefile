IDRIS2 = ../../../idris2boot
INTERACTIVE ?= --interactive

test:
	@../runtests $(IDRIS2) $(INTERACTIVE) --only $(only)

clean:
	find . -name '*.ibc' | xargs rm -f
	find . -name 'output' | xargs rm -f
