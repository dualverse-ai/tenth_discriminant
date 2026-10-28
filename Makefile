BOUND ?= 331

.PHONY: all verify clean
all verify clean:
	$(MAKE) -C bound-$(BOUND) $@
