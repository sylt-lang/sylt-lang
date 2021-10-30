MAIN := main.sy
RESOURCES := res

MAIN_LOVE = $(patsubst %.sy,%.love,$(MAIN))
SYLT := target/debug/sylt

.PHONY: all clean run $(SYLT)

all: $(MAIN_LOVE)

run: $(MAIN_LOVE)
	love $<

%.love: %.lua | build
	mv $< build/main.lua
	cp -r $(RESOURCES)/* build/
	zip -9 -j $@ build/*

%.lua: %.sy $(SYLT)
	$(SYLT) --compile $@ $<

$(SYLT):
	cargo build

clean:
	rm -rf *.lua
	rm -rf *.love
	rm -rf build

build:
	mkdir -p build
