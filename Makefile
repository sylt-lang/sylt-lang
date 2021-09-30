COMP := target/debug/sylt

.PHONY: clean

%.lua: %.sy $(COMP)
	@$(COMP) --lua $<
	@echo "------ RUN ------"
	@lua $@

clean:
	rm -rf *.lua
