BOUND ?= 498

.PHONY: all verify clean
all verify clean:
	$(MAKE) -C bound-$(BOUND) $@
