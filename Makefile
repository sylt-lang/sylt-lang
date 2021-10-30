BUILD := build
MAIN := main.sy
RESOURCES := res

MAIN_LOVE = $(patsubst %.sy,%.love,$(MAIN))
SYLT := target/debug/sylt

.PHONY: all clean run $(SYLT)

all: $(MAIN_LOVE)

run: $(MAIN_LOVE)
	love $<

%.love: %.lua | $(BUILD)
	mv $< $(BUILD)/main.lua
	cp -r $(RESOURCES)/* $(BUILD)/
	zip -9 -j $@ $(BUILD)/*

%.lua: %.sy $(SYLT)
	$(SYLT) --compile $@ $<

$(SYLT):
	cargo build

clean:
	rm -rf *.lua
	rm -rf *.love
	rm -rf $(BUILD)

$(BUILD):
	mkdir -p $@
