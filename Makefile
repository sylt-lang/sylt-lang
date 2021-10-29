SYLT := target/debug/sylt

.PHONY: all clean clean-lua $(SYLT) run-main

all: $(SYLT)

run-main: main.love
	love .

%.love: %.lua
	cp $< $@

%.lua: %.sy $(SYLT)
	$(SYLT) --compile $@ $<

$(SYLT):
	cargo build

clean: clean-lua
	cargo clean

clean-lua:
	rm -rf *.lua *.love
