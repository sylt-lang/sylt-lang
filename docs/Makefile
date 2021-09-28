BUILD := build
FILES := $(wildcard *.adoc)
STYLESHEET := stylesheet.css
TARGETS := $(patsubst %.adoc,$(BUILD)/%.html,$(FILES)) $(BUILD)/sylt.png

.PHONY: all clean

all: $(TARGETS)

$(BUILD)/%.html: %.adoc $(STYLESHEET) | $(BUILD)
	asciidoctor --out-file $@ $<

$(BUILD)/sylt.png: | $(BUILD)
	cp ../res/sylt.png $@

$(BUILD):
	mkdir -p $@

clean:
	rm -rf $(BUILD)
