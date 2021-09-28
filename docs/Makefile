BUILD := build
FILES := $(wildcard *.adoc)
TARGETS := $(patsubst %.adoc,$(BUILD)/%.html,$(FILES)) $(BUILD)/sylt.png
SYNTAX := ./syntax-highlighter.rb

.PHONY: all clean

all: $(TARGETS)

$(BUILD)/%.html: %.adoc $(SYNTAX) | $(BUILD)
	asciidoctor --require $(SYNTAX) --out-file $@ $<

$(BUILD)/sylt.png: | $(BUILD)
	cp ../res/sylt.png $@

$(BUILD):
	mkdir -p $@

clean:
	rm -rf $(BUILD)
