BUILD := build
FILES := $(wildcard *.adoc)
TARGETS := $(patsubst %.adoc,$(BUILD)/%.html,$(FILES)) $(BUILD)/sylt.png

.PHONY: all clean

all: $(TARGETS)

$(BUILD)/%.html: %.adoc | $(BUILD)
	asciidoctor --out-file $@ $<

$(BUILD)/sylt.png: | $(BUILD)
	cp ../res/sylt.png $@

$(BUILD):
	mkdir -p $@

clean:
	rm -rf $(BUILD)
